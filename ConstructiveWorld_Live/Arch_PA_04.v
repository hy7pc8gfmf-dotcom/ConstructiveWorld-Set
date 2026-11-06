(* ConstructiveWorld-Set -- statement-family compendium: rational bond-edge exchange and real-layer geometric budgets. *)

(** * Arch_PA_04: bond-edge exchange compendium and real-layer budget theorems.

    Mission.  Formalizes the rational bond and affine edge exchange family
      with iou issuance and redemption ([bond], [edge_spec], [edge_map],
      [edge_diss], [edge_bi], [edge_tame], [resolve], [resolve_total],
      [redeem_closes]), the real-layer [HlogZ] discharge ([hlogz_discharge],
      [hlogz_strict]), and the explicit iteration budget of geometric decay
      ([r_arch_pow_real], [budget_cond_sufficient], [geo_tail_budget]).

    Dependencies.  Stdlib [Lia], [List], [Extraction], [QArith.QArith],
      [QArith.Qabs].  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [UpConstitution] of this development.

    References.  This development, Arch_PA_04.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" Arch_PA_04.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
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
From Stdlib Require Import Extraction.

(* ================= Section 1. The ud_le_add_r family ================= *)
From Stdlib Require Import QArith.QArith QArith.Qabs.

Local Open Scope Q_scope.

(* A Q-layer micro-widget (bridged over UpConstitution; the right-addition weak order) *)

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

(* Section 2, item 1: the bond certificate -- a Set-level type for bounded coupon portfolios *)
(*   Currency body: the eps premise slot is the quantified resource of strictness (how much eps remains). *)

Record bond : Set := mk_bond {
  bd_id : nat;        (* statement id *)
  bd_bound : Q;       (* bound value: the upper bound not to be exceeded *)
  bd_eps : Q;         (* eps premise slot: the strictness slack *)
  bd_src : nat        (* issuing source: which metric/format *)
}.

(* The bond-face validator (Defined, executable; the inr branch carries a rejection code, mirroring the constitutional shape) *)
Inductive bond_reject : Set :=
| br_eps.              (* negative eps premise slot: no strictness slack left to cede *)

Definition bond_check (bd : bond)
  : Or (QleT' 0 (bd_eps bd)) (And (Id (Qle_bool 0 (bd_eps bd)) false) bond_reject) :=
  match Qle_bool 0 (bd_eps bd) as b
        return Or (Id b true) (And (Id b false) bond_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, br_eps)
  end.

(* Section 3, item 2: the exchange edge -- a conversion theorem as an affine reparametrization of eps *)
(*   eps_out = a * eps_in + b with a > 0 (a positive slope preserves the strict order). *)

Record edge_spec : Set := mk_edge {
  ed_id : nat;        (* edge id *)
  ed_src : nat;       (* source format (metric index) *)
  ed_dst : nat;       (* target format *)
  ed_a : Q;           (* slope a > 0 *)
  ed_b : Q            (* intercept b *)
}.

Definition edge_map (e : edge_spec) (x : Q) : Q := ed_a e * x + ed_b e.
Definition edge_diss (e : edge_spec) (x : Q) : Q := x - edge_map e x.
Definition edge_ok (e : edge_spec) : bool := Qlt_bool 0 (ed_a e).
Definition edge_bi (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool 0 (ed_b e)).
Definition edge_tame (e : edge_spec) : bool :=
  andb (Qlt_bool 0 (ed_a e)) (Qle_bool (ed_a e) 1).

(* The edge validator (Defined, executable; rejection-code shape) *)
Inductive edge_reject : Set :=
| er_slope.             (* nonpositive slope: the exchange does not preserve the strict order *)

Definition edge_check (e : edge_spec)
  : Or (QltT 0 (ed_a e)) (And (Id (Qlt_bool 0 (ed_a e)) false) edge_reject) :=
  match Qlt_bool 0 (ed_a e) as b
        return Or (Id b true) (And (Id b false) edge_reject) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, er_slope)
  end.

(* Boolean-gate certificate extraction: the two Q facts of a regular edge (a > 0 and b >= 0) *)
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

(* The two Q facts of a tame edge (a > 0 and a <= 1) *)
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

(* Order property of the edge as conversion theorem: a > 0 makes the affine eps reparametrization strictly order-preserving *)
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

(* A regular edge keeps the eps premise slot strictly positive (strictness is not annihilated by the exchange) *)
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
    apply Qle_to_QleT'.
    apply (Qle_plus_nonneg_r (ed_a e * x) (ed_b e)).
    exact (QleT'_to_Qle _ _ Hb).
Qed.

(* Exchanging a bond along an edge: the eps premise slot is reparametrized by the affine map *)
Definition bond_exchange (e : edge_spec) (bd : bond) : bond :=
  mk_bond (bd_id bd) (bd_bound bd) (edge_map e (bd_eps bd)) (ed_dst e).

Lemma bond_exchange_eps : forall (e : edge_spec) (bd : bond),
  bd_eps (bond_exchange e bd) == edge_map e (bd_eps bd).
Proof. intros e bd. reflexivity. Qed.

(* Currency conservation at the bond level: incoming eps = outgoing eps + dissipation *)
Theorem bond_exchange_conservation : forall (e : edge_spec) (bd : bond),
  bd_eps bd == bd_eps (bond_exchange e bd) + edge_diss e (bd_eps bd).
Proof.
  intros e bd. rewrite bond_exchange_eps.
  unfold edge_diss, edge_map. ring.
Qed.

(* The exchange preserves strictness: a regular edge keeps the exchanged eps premise slot strictly positive *)
Theorem bond_exchange_pos : forall (e : edge_spec) (bd : bond),
  Id (edge_bi e) true -> QltT 0 (bd_eps bd) ->
  QltT 0 (bd_eps (bond_exchange e bd)).
Proof.
  intros e bd Hbi Hx.
  unfold bond_exchange.
  apply (edge_map_pos e (bd_eps bd) Hx Hbi).
Qed.

(* Section 4, item 3 (main item): edge_compound_affine -- composing edges is composing their affine eps maps *)
(*   the composite slope is a2 * a1 > 0 (constant positivity, linearly decidable); *)
(*   path legality is positivity of the affine composite, decided linearly by the Boolean decider path2_ok. *)

Definition edge_comp (e2 e1 : edge_spec) : edge_spec :=
  mk_edge (ed_id e1) (ed_src e1) (ed_dst e2)
          (ed_a e2 * ed_a e1) (ed_a e2 * ed_b e1 + ed_b e2).

Lemma edge_comp_slope : forall e1 e2 : edge_spec,
  ed_a (edge_comp e2 e1) == ed_a e2 * ed_a e1.
Proof. intros e1 e2. reflexivity. Qed.

Lemma edge_comp_b : forall e1 e2 : edge_spec,
  ed_b (edge_comp e2 e1) == ed_a e2 * ed_b e1 + ed_b e2.
Proof. intros e1 e2. reflexivity. Qed.

(* Main item: the eps map of a composite edge is the affine composite of the two edge maps (path-semantics correctness) *)
Theorem edge_compound_affine : forall (e1 e2 : edge_spec) (x : Q),
  edge_map (edge_comp e2 e1) x == edge_map e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* Composition legality: positive slopes on both edges give a positive composite slope *)
Theorem edge_comp_legal : forall e1 e2 : edge_spec,
  QltT 0 (ed_a e1) -> QltT 0 (ed_a e2) -> QltT 0 (ed_a (edge_comp e2 e1)).
Proof.
  intros e1 e2 H1 H2.
  apply Qlt_to_QltT.
  apply (Qmult_lt_0_compat (ed_a e2) (ed_a e1)           (QltT_to_Qlt 0 (ed_a e2) H2) (QltT_to_Qlt 0 (ed_a e1) H1)).
Qed.

(* The linear (Boolean) decider of path legality: two-segment paths *)
Definition path2_ok (e2 e1 : edge_spec) : bool :=
  andb (edge_ok e1) (edge_ok e2).

(* Decider soundness: Boolean truth gives a positive composite slope (linearly decidable legality) *)
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

(* The composite of tame edges stays tame (slope product <= 1) -- the dissipation account closes along paths *)
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
      - apply (Qmult_le_compat_r (ed_a e1) 1 (ed_a e2) (QleT'_to_Qle _ _ Hb1)).
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

(* Section 5, item 4: the dissipation account path_dissipation *)
(*   Currency semantics: eps is a conserved quantity -- every exchange satisfies eps_in = eps_out + dissipation; *)
(*   dissipation is additive along paths (no double counting, no minting out of nothing); *)
(*   the dissipation of a tame edge (a <= 1) is monotone in the incoming eps (larger exchanges dissipate more). *)

(* The currency conservation identity *)
Theorem diss_conservation : forall (e : edge_spec) (x : Q),
  x == edge_map e x + edge_diss e x.
Proof.
  intros e x. unfold edge_diss, edge_map. ring.
Qed.

(* Additivity of path dissipation: the total dissipation of a composite path is the sum of the segment dissipations (a telescoping identity) *)
Theorem path_dissipation_additive : forall (e1 e2 : edge_spec) (x : Q),
  edge_diss (edge_comp e2 e1) x == edge_diss e1 x + edge_diss e2 (edge_map e1 x).
Proof.
  intros e1 e2 x. unfold edge_diss, edge_map.
  rewrite edge_comp_slope. rewrite edge_comp_b. ring.
Qed.

(* Monotonicity of path dissipation: on a tame edge a larger incoming eps dissipates more *)
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

(* Path-level corollary: dissipation stays monotone after composing two tame edges *)
Theorem path_dissipation_mono_compound : forall (e1 e2 : edge_spec) (x y : Q),
  Id (edge_tame e1) true -> Id (edge_tame e2) true -> Qle y x ->
  Qle (edge_diss (edge_comp e2 e1) y) (edge_diss (edge_comp e2 e1) x).
Proof.
  intros e1 e2 x y H1 H2 Hyx.
  apply (path_dissipation_mono (edge_comp e2 e1) x y).
  - apply edge_tame_comp; assumption.
  - exact Hyx.
Qed.

(* Section 6, item 5: the iou -- a query miss issues a gap obligation (re-enterable) *)
(*   Mirroring the inr rejection-code shape of the constitutional check_claim: the inr payload of resolve is the iou. *)
(*   A hit is an executable certificate chain (format continuation + positive slope + dissipation within budget + positive output); *)
(*   A miss is an iou (the gap from->to, the dissipation budget delta, the eps premise slot, the back-referenced query id). *)

Record query : Set := mk_query {
  qr_id : nat;        (* query id *)
  qr_from : nat;      (* format held *)
  qr_to : nat;        (* format requested *)
  qr_eps : Q;         (* incoming eps (held-coupon premise slot) *)
  qr_delta : Q        (* dissipation budget delta *)
}.

Record iou : Set := mk_iou {
  iou_from : nat;     (* gap source format *)
  iou_to : nat;       (* gap target format *)
  iou_eps : Q;        (* the eps premise slot to be replayed *)
  iou_delta : Q;      (* dissipation budget delta *)
  iou_ref : nat       (* back-referenced query id: once redeemed, the new edge grows into the graph *)
}.

(* iou issuance: the gap obligation of a query (the only product of a miss; no error is raised) *)
Definition iou_issue (q : query) : iou :=
  mk_iou (qr_from q) (qr_to q) (qr_eps q) (qr_delta q) (qr_id q).

(* The Boolean gate: true yields the proof Id b true, false yields the payload (Id b false, iou) *)
Definition bool_gate (b : bool) (w : iou) : Or (Id b true) (And (Id b false) iou) :=
  match b as x return Or (Id x true) (And (Id x false) iou) with
  | true => inl (@id_refl bool true)
  | false => inr (@id_refl bool false, w)
  end.

(* The five doors (Defined, executable): format continuation src/dst, positive slope, dissipation within budget, positive output *)
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

(* The hit certificate: a package of five proofs (all Set-level Id-of-bool, extractable) *)
Definition hit_cert (e : edge_spec) (q : query) : Set :=
  And (And (Id (Nat.eqb (ed_src e) (qr_from q)) true)
           (Id (Nat.eqb (ed_dst e) (qr_to q)) true))
      (And (Id (Qlt_bool 0 (ed_a e)) true)
           (And (Id (Qle_bool (edge_diss e (qr_eps q)) (qr_delta q)) true)
                (Id (Qlt_bool 0 (edge_map e (qr_eps q))) true))).

(* Single-edge exchange decision: all doors passing issues a certificate, any door failing issues an iou (inr with payload) *)
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

(* The bridge from Nat.eqb truth to the Set-level Id of Leibniz equality *)
Lemma nat_eqb_id : forall (x y : nat), Id (Nat.eqb x y) true -> Id x y.
Proof.
  intro x. induction x as [| x IH]; intros y H; destruct y as [| y]; simpl in H.
  - apply id_refl.
  - inversion H.
  - inversion H.
  - apply (RealSetoid.eq_Id (Nat.succ x) (Nat.succ y)).
    f_equal. apply RealSetoid.Id_eq. apply IH. exact H.
Qed.

(* Semantic shape of the hit certificate: direct proofs of format continuation plus the Q-layer facts *)
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

(* The payload of the rejection branch of the Boolean gate is always the iou itself *)
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

(* Item 5 main theorem: a single-edge miss gives an iou carrying the gap obligation (from/to/eps/delta all back-referencing the query) *)
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

(* The graph scan (Defined, executable): find the first serving edge under the format key (from,to) *)
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

(* Graph-level exchange: Some e takes the single-edge decision, None issues an iou *)
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

(* Totality of the decision: every query yields a hit or an iou (mirroring the constitutional check_claim_total) *)
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

(* Item 5, graph-level form: a miss gives an iou carrying the gap obligation *)
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

(* Hit soundness: a hit gives a strictly positive outgoing eps with dissipation within budget (executable certificate semantics) *)
Theorem resolve_hit_sound : forall (g : list edge_spec) (q : query)
                                   (e : edge_spec) (w : hit_cert e q),
  Id (resolve g q) (inl (existT _ e w)) ->
  And (QltT 0 (edge_map e (qr_eps q)))
      (QleT' (edge_diss e (qr_eps q)) (qr_delta q)).
Proof.
  intros g q e w _. destruct w as [_ [_ [h4 h5]]].
  split; assumption.
Qed.

(* Section 6b, item 5b: iou re-entry -- redeem (justification) and reissue (obligation persistence) *)
(*   redeem io e issues a certificate when e closes the gap of io (the new edge may grow into the graph); *)
(*   when the exchange fails a door, the iou re-enters unchanged (the obligation persists and may be retried with a new edge). *)

Definition iou_query (io : iou) : query :=
  mk_query (iou_ref io) (iou_from io) (iou_to io) (iou_eps io) (iou_delta io).

Definition dis_redeem (io : iou) (e : edge_spec) : Or (hit_cert e (iou_query io)) iou :=
  resolve1 e (iou_query io).

(* Re-entry: a rejection by dis_redeem returns an iou whose gap fields agree pointwise with the original (obligation persistence) *)
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

(* Justification: an iou closed by a new edge gives a graph grown by that edge and a hit on the original query (the graph growth theorem) *)
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

(* The decision report (non-dependent form: no sigT, extractable as a whole; vm_compute friendly) *)

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

(* Section 7, item 6: the vm_compute numeric self-test -- a 3-edge graph with the chain eps/2 -> eps/4 -> eps/8 *)
(*   The graph is 3 primitive half-dissipating edges plus 2 composite edges (composite closure makes the routing reachable). *)

(* Primitive edges fmt0->fmt1->fmt2->fmt3, each segment halving eps (a = 1/2, b = 0, zero injection) *)
Definition e_h1 : edge_spec := mk_edge 1 0 1 (1#2) 0.
Definition e_h2 : edge_spec := mk_edge 2 1 2 (1#2) 0.
Definition e_h3 : edge_spec := mk_edge 3 2 3 (1#2) 0.

(* Composite edges grown into the graph: ec12 : fmt0->fmt2 with slope 1/4; ec123 : fmt0->fmt3 with slope 1/8 *)
Definition ec12 : edge_spec := edge_comp e_h2 e_h1.
Definition ec123 : edge_spec := edge_comp e_h3 ec12.

Definition atlas3 : list edge_spec := e_h1 :: e_h2 :: e_h3 :: ec12 :: ec123 :: nil.

(* Query 7: holds fmt0 with eps premise slot 1, requests fmt3, dissipation budget delta = 1 -- hits ec123 *)
Definition q_chain : query := mk_query 7 0 3 1 1.
(* Query 8: fmt3->fmt0 has no edge at all -- a miss, an iou is issued *)
Definition q_back : query := mk_query 8 3 0 1 1.
(* Query 9: fmt0->fmt3 but budget delta = 1/2 -- the dissipation 7/8 exceeds the budget, an iou (the gap obligation) *)
Definition q_tight : query := mk_query 9 0 3 1 (1#2).

(* Chain hit: the outgoing eps is 1/8 (eps -> eps/8), the certificate is executable *)
Theorem demo_chain_hit : Id (resolve_report atlas3 q_chain) (rv_hit ec123 (1#8)).
Proof. vm_compute. reflexivity. Qed.

(* The path dissipation value: 1 - 1/8 = 7/8 (additive accounting: 1/2 + (3/4) as the segment dissipation sum) *)
Theorem demo_diss_total : Id (Qred (edge_diss ec123 1)) (7#8).
Proof. vm_compute. reflexivity. Qed.

Theorem demo_diss_steps : edge_diss ec123 1
  == edge_diss ec12 1 + edge_diss e_h3 (edge_map ec12 1).
Proof. vm_compute. reflexivity. Qed.

(* A numeric instance of the currency conservation identity: 1 = 1/8 + 7/8 *)
Theorem demo_conservation : 1 == edge_map ec123 1 + edge_diss ec123 1.
Proof. vm_compute. reflexivity. Qed.

(* The reverse query finds no edge: a miss gives an iou (gap fmt3->fmt0, back-referencing query 8) *)
Theorem demo_miss_back : Id (resolve_report atlas3 q_back)
  (rv_miss (mk_iou 3 0 1 1 8)).
Proof. vm_compute. reflexivity. Qed.

(* Insufficient budget: dissipation 7/8 > delta = 1/2 gives an iou (gap fmt0->fmt3, back-referencing query 9) *)
Theorem demo_tight_iou : Id (resolve_report atlas3 q_tight)
  (rv_miss (mk_iou 0 3 1 (1#2) 9)).
Proof. vm_compute. reflexivity. Qed.

(* Item 5b numeric self-test: iou re-entry -- a good-edge exchange closes the gap and the new edge grows into the graph *)

Definition demo_io_tight : iou := mk_iou 0 3 1 (1#2) 9.

(* The good edge: fmt0->fmt3 with slope 15/16 -- dissipation 1/16 <= 1/2 and outgoing 15/16 > 0 *)
Definition e_good : edge_spec := mk_edge 4 0 3 (15#16) 0.

(* dis_redeem: the iou demo_io_tight is justified by e_good (all five proofs pass) *)
Definition cert_good : hit_cert e_good (iou_query demo_io_tight) :=
  ((@id_refl bool true, @id_refl bool true),
   (@id_refl bool true, (@id_refl bool true, @id_refl bool true))).

Theorem demo_redeem_ok : Id (dis_redeem demo_io_tight e_good) (inl cert_good).
Proof. vm_compute. reflexivity. Qed.

(* A numeric instance of redeem_closes: with the new edge grown into the graph, the original query 9 hits e_good *)
Definition atlas4 : list edge_spec := e_good :: atlas3.

Theorem demo_growth_closes :
  Id (resolve_report atlas4 q_tight) (rv_hit e_good (15#16)).
Proof. vm_compute. reflexivity. Qed.

(* A numeric instance of the re-entry form: a bad edge (a negative intercept swallowing the eps premise slot) fails to justify, and the iou is returned unchanged *)
Definition e_bad : edge_spec := mk_edge 5 0 3 (15#16) (-1).

Theorem demo_redeem_reissue :
  sigT (fun r => Id (dis_redeem demo_io_tight e_bad) (inr r)).
Proof.
  exists (iou_issue (iou_query demo_io_tight)).
  unfold dis_redeem. vm_compute. reflexivity.
Qed.

(* Section 8: the decision report output (the sample source of the G3 self-test) *)

Eval vm_compute in resolve_report atlas3 q_chain.
Eval vm_compute in resolve_report atlas3 q_back.
Eval vm_compute in resolve_report atlas3 q_tight.
Eval vm_compute in resolve_report atlas4 q_tight.
Eval vm_compute in edge_diss ec123 1.
Eval vm_compute in bond_check (mk_bond 1 (3#2) (1#4) 0).
Eval vm_compute in edge_check e_good.

Print Assumptions edge_comp_legal.
Print Assumptions edge_comp_b.
Print Assumptions edge_comp_slope.
Print Assumptions bond_exchange_pos.
Print Assumptions bond_exchange_eps.
(* ================= Section 2. The hlogz_discharge family ================= *)
(* ---------- G01_CoreMicro ---------- *)
Set Extraction Output Directory ".".
(*  -- the Real-layer collective discharge of the HlogZ premise of the root KLProjection main theorem *)
(* Goal: the explicit premise HlogZ of projected_distribution_minimizes_kl *)
(*   HlogZ : le (log Z_aud) zero, holds unconditionally at the Real layer: *)
(*   Z_aud <= 1 (Z_aud_le_one, proved in the root) *)
(*   ⟹ log Z_aud ≤ log 1 = 0                                      *)
(*     the le-monotone form of log is G01_CoreMicro.real_log_le_mono; *)
(*     log 1 == 0 is real_log_one, proved in the root. *)
(* Inventory of results: *)
(*   hlogz_discharge       -- the main proof: 0 < Z <= 1 gives log Z <= 0 *)
(*   hlogz_discharge_full  -- the same-shape aligned version (the direct G01_CoreMicro form) *)
(*   hlogz_strict          -- the strict version: 0 < Z < 1 gives log Z < 0 *)
(*                            (the filter does intercept mass) *)
(*   hlogz_opp_nonneg      -- the KL tail form: 0 <= opp (log Z) *)
(*                            (the direct input of opp_le_compat in the main theorem proof) *)
(* Every statement is Real-layer and Set-level (real_lt / real_le / real_eq, Or encoding), *)
(* purely constructive, closed by Qed throughout, and extractable. *)


(* Main result 1: the HlogZ proof (a direct route through the le-monotone form of log) *)
(*   Argument: 0 < Za and Za <= 1 give real_log Za <= real_log 1 == 0. *)
(*   real_log_le_mono : real_le a b -> real_le (log a) (log b)       *)
(*   (the positivity premises on a and b come from HZa and real_lt_zero_one). *)
Theorem hlogz_discharge :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  (* The le chain composed through the middle term real_log 1 *)
  apply (real_le_trans _ (real_log real_one Hone) _).
  - (* The monotone le form: Za <= 1 gives log Za <= log 1 *)
    exact (real_log_le_mono Za real_one HZa Hone HZa1).
  - (* log 1 == 0 is lifted to le through the eq-to-le bridge (the inr branch) *)
    exact (real_eq_le_bridge (real_log real_one Hone) real_zero
             (real_log_one Hone)).
Qed.

(* Main result 2: the full HlogZ proof (aligned with the KLProjection premise) *)
(*   The same-shape statement, taking the direct G01_CoreMicro form real_log_le_zero_of_le_one; *)
(*   the two routes (monotone-chain composition and the direct form) reach the same goal. *)
Theorem hlogz_discharge_full :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  exact (real_log_le_zero_of_le_one Za HZa HZa1).
Qed.

(* Additional result 1: the strict version -- the filter does intercept mass *)
(*   0 < Za < 1 gives log Za < log 1 = 0 (a strict lt chain). *)
(*   real_log_lt_mono is stated about cw_log; after the definitional unfolding of real_log (:= cw_log) *)
(*   the terms align pointwise, and the tail replaces log 1 by 0 through real_lt_eq_lt. *)
Theorem hlogz_strict :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_lt Za real_one),
  real_lt (real_log Za HZa) real_zero.
Proof.
  intros Za HZa HZa1.
  assert (Hone : real_lt real_zero real_one) by exact real_lt_zero_one.
  apply (real_lt_eq_lt _ (cw_log real_one Hone) _).
  - (* Strict monotonicity: Za < 1 gives cw_log Za < cw_log 1 *)
    unfold real_log.
    exact (real_log_lt_mono Za real_one HZa Hone HZa1).
  - (* cw_log 1 == 0 *)
    exact (real_log_one Hone).
Qed.

(* Additional result 2: the KL tail form -- 0 <= opp (log Z) *)
(*   The direct Real-layer supply of the tail term T == opp (log Z_aud) >= 0 inside the main theorem proof: *)
(*   log Z <= 0 is contravariant through opp (real_opp_le_compat), giving opp 0 <= opp (log Z); *)
(*   then composed with the eq-to-le bridge of opp 0 == 0 (the inl branch? no, the inr branch). *)
Theorem hlogz_opp_nonneg :
  forall (Za : Real) (HZa : real_lt real_zero Za) (HZa1 : real_le Za real_one),
  real_le real_zero (real_opp (real_log Za HZa)).
Proof.
  intros Za HZa HZa1.
  apply (real_le_trans _ (real_opp real_zero) _).
  - (* 0 <= opp 0: symmetry of eq, then lift to le *)
    exact (real_eq_le_bridge real_zero (real_opp real_zero)
             (real_eq_sym (real_opp real_zero) real_zero real_opp_zero)).
  - (* opp 0 <= opp (log Z): contravariance plus main result 1 *)
    exact (real_opp_le_compat (real_log Za HZa) real_zero
             (hlogz_discharge Za HZa HZa1)).
Qed.

(* The extraction check (warning silencing: the transparency-bypass access-list notice, by the same method as UpGRPO) *)
Set Warnings "-extraction-opaque-accessed".

Extraction "uphlogz.ml" hlogz_discharge hlogz_strict hlogz_opp_nonneg.

(* ---------- UpSigMigrate ---------- *)
Module SigMigrate.
(*  -- the abstract-layer signature adaptation pilot: from the Id family to the setoid family (req := real_eq).
   Pilot 1 (required): req_free_energy_kl_decomp -- the setoid-signature version of
     F[p] == F[p_b] + D * KL(p||p_b): the Section Context becomes RealInterfaceEnhancedSetoid;
     Id migrates to req throughout; normalized := req (sum p) one; the log family carries positivity premises.
   Pilot 2 (best effort): req_attention_is_gibbs_temp -- three premises and the pointwise conclusion, all req.
   Discipline: purely constructive; Set level (req/lt/le are Set-valued, statements carry zero Prop);
   intermediate equations all go through the req fields (req_trans chains plus compat bridges); destruct elimination is unavailable. *)
Import RealInterfaceEnhancedMod.
(* Interface adaptation (module-scoped): the interface class in this tree is unparameterized;
   its carrier is the global Real (S07_RealSetoidExpLog.v:8075 zero-argument Class
   RealInterfaceEnhancedSetoid plus the global Instance RealEnhancedReal).  The parameterized
   section binders Context {R : Set} {RIS : RealInterfaceEnhancedSetoid R}. are removed from
   both pilot sections, and the field names below resolve through the concrete global twins
   (the bindings the instance assigns), the world's own UpReqAlign3.v precedent spelled with
   the Abbreviation vernacular.  Statement names and proof bodies are unchanged apart from
   the dropped binder arguments. *)
Abbreviation R := Real.
Abbreviation req := real_eq.
Abbreviation req_refl := real_eq_refl.
Abbreviation req_sym := real_eq_sym.
Abbreviation req_trans := real_eq_trans.
Abbreviation zero := real_zero.
Abbreviation one := real_one.
Abbreviation plus := real_plus.
Abbreviation mult := real_mult.
Abbreviation opp := real_opp.
Abbreviation lt := real_lt.
Abbreviation le := real_le.
Abbreviation req_plus_compat := RealSetoid.real_eq_plus_compat_adapt.
Abbreviation req_mult_compat := RealSetoid.real_eq_mult_compat_adapt.
Abbreviation req_opp_compat := RealSetoid.real_eq_opp_compat.
Abbreviation plus_assoc := real_plus_assoc.
Abbreviation plus_comm := real_plus_comm.
Abbreviation plus_zero := real_plus_zero.
Abbreviation plus_opp := real_plus_opp.
Abbreviation mult_assoc := real_mult_assoc.
Abbreviation mult_comm := real_mult_comm.
Abbreviation mult_one := real_mult_one.
Abbreviation distrib := real_distrib.
Abbreviation mult_zero := real_mult_zero.
Abbreviation inv_pos := real_inv_pos.
Abbreviation inv_pos_correct := real_inv_pos_correct.
Abbreviation inv_pos_pos := real_inv_pos_pos.
Abbreviation inv_pos_ext := real_inv_pos_ext.
Abbreviation mult_positive := real_mult_positive.
Abbreviation exp_neg := real_exp_neg.
Abbreviation exp_neg_pos := real_exp_neg_pos.
Abbreviation log := real_log.

(* Pilot 1: the setoid-signature adaptation of the FreeEnergyMinimization section *)
(*   Id original: CW L15759-16440 (Context {RI : RealInterfaceEnhanced}; *)
(*   StateSpace/SumOver are Id-family classes whose fields carry Id, so this pilot declares *)
(*   the three req-signature sum properties as the section premise positions (the setoid *)
(*   adaptation face of the SumOver class); the adaptation cost is recorded in the report; the two proved upstream *)
(*   Id-family lemmas (energy_in_log_boltzmann / free_energy_boltzmann) are carried by *)
(*   req-signature bridge premise positions; the full-migration extrapolation is in the report. *)
Section ReqFreeEnergyPilot.
Variable S : Set.

(* ---- The req-signature adaptation face of SumOver (the setoid copy of the Id-family SumOver, L1400) ---- *)
Variable sumf : (S -> R) -> R.
Hypothesis sum_ext :
  forall f g : S -> R, (forall s : S, req (f s) (g s)) -> req (sumf f) (sumf g).
Hypothesis sum_add :
  forall f g : S -> R,
    req (sumf (fun s => plus (f s) (g s))) (plus (sumf f) (sumf g)).
Hypothesis sum_linear :
  forall (a : R) (f : S -> R),
    req (sumf (fun s => mult a (f s))) (mult a (sumf f)).

(* ---- Section data (aligned with the Id-family L15778-15791) ---- *)
Variable base_loss : S -> R.
Variable D : R.
Variable D_pos : lt zero D.
Variable Z : R.
Variable Z_pos : lt zero Z.
Hypothesis partition_condition :
  req Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).

(* ---- In-section definitions (the setoid conventional shape) ---- *)
Definition cwe_positive_dist (p : S -> R) : Set := forall s : S, lt zero (p s).
Definition cwe_boltzmann_dist : S -> R :=
  fun s => mult (inv_pos Z Z_pos) (exp_neg (mult (inv_pos D D_pos) (base_loss s))).
(* The log family carries positivity premises (setoid interface L40570), so free_energy is restricted to positive distributions *)
Definition cwe_free_energy (p : S -> R) (Hp : cwe_positive_dist p) : R :=
  plus (sumf (fun s => mult (p s) (base_loss s)))
       (mult D (sumf (fun s => mult (p s) (log (p s) (Hp s))))).
Definition cwe_normalized (p : S -> R) : Set := req (sumf p) one.
Definition rminus (a b : R) : R := plus a (opp b).

(* ---- Positivity of the Boltzmann distribution (required by the setoid log premise; assembled directly from interface fields) ---- *)
Lemma req_boltzmann_positive : cwe_positive_dist cwe_boltzmann_dist.
Proof.
  intro s.
  apply mult_positive.
  - apply inv_pos_pos.
  - apply exp_neg_pos.
Qed.

(* ---- The req-signature bridges for the proved upstream Id-family results (Id originals L16116 / L15945) ---- *)
Hypothesis energy_in_log_boltzmann_bridge :
  forall s : S,
    req (base_loss s)
        (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))
                           (log Z Z_pos)))).
Hypothesis free_energy_boltzmann_bridge :
  req (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
      (mult (opp D) (log Z Z_pos)).

(* A. Algebraic prelude: the req-version opp algebra (pure derivation from interface fields, zero destruct, *)
(*    entirely req_trans chains plus compat bridges -- the Id-family rewrite elimination is unavailable) *)

(* The right add-zero form: the plus_zero field only has the left form; the right form goes through the comm bridge *)
Lemma req_plus_zero_r : forall a : R, req (plus zero a) a.
Proof.
  intro a.
  exact (req_trans (plus zero a) (plus a zero) a (plus_comm zero a) (plus_zero a)).
Qed.

(* The left multiply-by-one form: the mult_one field only has the right form *)
Lemma req_mult_one_l : forall a : R, req (mult one a) a.
Proof.
  intro a.
  exact (req_trans (mult one a) (mult a one) a (mult_comm one a) (mult_one a)).
Qed.

(* Left cancellation: the engine of opp uniqueness (free in the Id family through destruct/injection; a 7-segment chain here) *)
Lemma req_add_cancel_l : forall (u v w : R),
  req (plus u v) (plus w v) -> req u w.
Proof.
  intros u v w H.
  apply (req_trans u (plus u zero) w).
  - apply (req_sym (plus u zero) u). apply plus_zero.
  - apply (req_trans (plus u zero) (plus u (plus v (opp v))) w).
    + apply (req_plus_compat u u zero (plus v (opp v))).
      * apply req_refl.
      * apply (req_sym (plus v (opp v)) zero). apply plus_opp.
    + apply (req_trans (plus u (plus v (opp v))) (plus (plus u v) (opp v)) w).
      * apply plus_assoc.
      * apply (req_trans (plus (plus u v) (opp v)) (plus (plus w v) (opp v)) w).
        -- apply (req_plus_compat (plus u v) (plus w v) (opp v) (opp v) H).
           apply req_refl.
        -- apply (req_trans (plus (plus w v) (opp v)) (plus w (plus v (opp v))) w).
           ++ apply (req_sym (plus w (plus v (opp v))) (plus (plus w v) (opp v))).
              apply plus_assoc.
           ++ apply (req_trans (plus w (plus v (opp v))) (plus w zero) w).
              ** apply (req_plus_compat w w (plus v (opp v)) zero).
                 --- apply req_refl.
                 --- apply plus_opp.
              ** apply plus_zero.
Qed.

(* Double negation: opp (opp a) == a (two uses of plus_opp plus cancellation; the Id-family double_neg lemma) *)
Lemma req_double_neg : forall a : R, req (opp (opp a)) a.
Proof.
  intro a.
  apply (req_add_cancel_l (opp (opp a)) (opp a) a).
  apply (req_trans (plus (opp (opp a)) (opp a)) zero (plus a (opp a))).
  - apply (req_trans (plus (opp (opp a)) (opp a)) (plus (opp a) (opp (opp a))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus a (opp a)) zero). apply plus_opp.
Qed.

(* Negation distributes: opp (a+b) == opp a + opp b (the Id-family opp_plus lemma) *)
Lemma req_opp_plus : forall a b : R, req (opp (plus a b)) (plus (opp a) (opp b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (opp (plus a b)) (plus a b) (plus (opp a) (opp b))).
  apply (req_trans (plus (opp (plus a b)) (plus a b)) zero (plus (plus (opp a) (opp b)) (plus a b))).
  - apply (req_trans (plus (opp (plus a b)) (plus a b)) (plus (plus a b) (opp (plus a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
  - apply (req_sym (plus (plus (opp a) (opp b)) (plus a b)) zero).
    apply (req_trans (plus (plus (opp a) (opp b)) (plus a b))
                     (plus (opp a) (plus (opp b) (plus a b)))
                     zero).
    + apply (req_sym (plus (opp a) (plus (opp b) (plus a b)))
                     (plus (plus (opp a) (opp b)) (plus a b))).
      apply plus_assoc.
    + apply (req_trans (plus (opp a) (plus (opp b) (plus a b)))
                       (plus (opp a) (plus (plus (opp b) a) b))
                       zero).
      * apply (req_plus_compat (opp a) (opp a) (plus (opp b) (plus a b)) (plus (plus (opp b) a) b)).
        -- apply req_refl.
        -- apply plus_assoc.
      * apply (req_trans (plus (opp a) (plus (plus (opp b) a) b))
                         (plus (opp a) (plus (plus a (opp b)) b))
                         zero).
        -- apply (req_plus_compat (opp a) (opp a) (plus (plus (opp b) a) b) (plus (plus a (opp b)) b)).
           ++ apply req_refl.
           ++ apply (req_plus_compat (plus (opp b) a) (plus a (opp b)) b b).
              ** apply plus_comm.
              ** apply req_refl.
        -- apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                            (plus (plus (opp a) a) (plus (opp b) b))
                            zero).
           ++ apply (req_trans (plus (opp a) (plus (plus a (opp b)) b))
                               (plus (opp a) (plus a (plus (opp b) b)))
                               (plus (plus (opp a) a) (plus (opp b) b))).
              ** apply (req_plus_compat (opp a) (opp a) (plus (plus a (opp b)) b) (plus a (plus (opp b) b))).
                 --- apply req_refl.
                 --- apply (req_sym (plus a (plus (opp b) b)) (plus (plus a (opp b)) b)). apply plus_assoc.
              ** apply plus_assoc.
           ++ apply (req_trans (plus (plus (opp a) a) (plus (opp b) b)) (plus zero zero) zero).
              ** apply (req_plus_compat (plus (opp a) a) zero (plus (opp b) b) zero).
                 --- apply (req_trans (plus (opp a) a) (plus a (opp a)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
                 --- apply (req_trans (plus (opp b) b) (plus b (opp b)) zero).
                     +++ apply plus_comm.
                     +++ apply plus_opp.
              ** apply plus_zero.
Qed.

(* mult a (opp b) == opp (mult a b) (the Id-family opp_mult_l lemma) *)
Lemma req_mult_opp_l : forall a b : R, req (mult a (opp b)) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_add_cancel_l (mult a (opp b)) (mult a b) (opp (mult a b))).
  apply (req_trans (plus (mult a (opp b)) (mult a b)) zero (plus (opp (mult a b)) (mult a b))).
  - apply (req_trans (plus (mult a (opp b)) (mult a b)) (plus (mult a b) (mult a (opp b))) zero).
    + apply plus_comm.
    + apply (req_trans (plus (mult a b) (mult a (opp b))) (mult a (plus b (opp b))) zero).
      * apply (req_sym (mult a (plus b (opp b))) (plus (mult a b) (mult a (opp b)))).
        apply distrib.
      * apply (req_trans (mult a (plus b (opp b))) (mult a zero) zero).
        -- apply (req_mult_compat a a (plus b (opp b)) zero).
           ++ apply req_refl.
           ++ apply plus_opp.
        -- apply mult_zero.
  - apply (req_sym (plus (opp (mult a b)) (mult a b)) zero).
    apply (req_trans (plus (opp (mult a b)) (mult a b)) (plus (mult a b) (opp (mult a b))) zero).
    + apply plus_comm.
    + apply plus_opp.
Qed.

(* mult (opp a) b == opp (mult a b) (the Id-family opp_mult_r lemma, through the comm bridge) *)
Lemma req_opp_mult_l : forall a b : R, req (mult (opp a) b) (opp (mult a b)).
Proof.
  intros a b.
  apply (req_trans (mult (opp a) b) (mult b (opp a)) (opp (mult a b))).
  - apply mult_comm.
  - apply (req_trans (mult b (opp a)) (opp (mult b a)) (opp (mult a b))).
    + apply req_mult_opp_l.
    + apply (req_opp_compat (mult b a) (mult a b)). apply mult_comm.
  Qed.

(* B. Summation-layer req lemmas (transliterations over the SumOver req adaptation face) *)

(* sum (opp f) == opp (sum f) (the Id original L15801 sum_opp) *)
Lemma req_sum_opp :
  forall f : S -> R, req (sumf (fun s => opp (f s))) (opp (sumf f)).
Proof.
  intro f.
  apply (req_trans (sumf (fun s => opp (f s)))
                   (sumf (fun s => mult (opp one) (f s)))
                   (opp (sumf f))).
  - apply (sum_ext (fun s => opp (f s)) (fun s => mult (opp one) (f s))).
    intro s.
    apply (req_trans (opp (f s)) (opp (mult one (f s))) (mult (opp one) (f s))).
    + apply (req_opp_compat (f s) (mult one (f s))).
      apply (req_sym (mult one (f s)) (f s)). apply req_mult_one_l.
    + apply (req_sym (mult (opp one) (f s)) (opp (mult one (f s)))).
      apply req_opp_mult_l.
  - apply (req_trans (sumf (fun s => mult (opp one) (f s)))
                     (mult (opp one) (sumf f))
                     (opp (sumf f))).
    + apply (sum_linear (opp one) f).
    + apply (req_trans (mult (opp one) (sumf f)) (opp (mult one (sumf f))) (opp (sumf f))).
      * apply req_opp_mult_l.
      * apply (req_opp_compat (mult one (sumf f)) (sumf f)). apply req_mult_one_l.
Qed.

(* Normalization of the Boltzmann distribution (the req version of the Id original L15846 boltzmann_normalized) *)
Lemma req_boltzmann_normalized : req (sumf cwe_boltzmann_dist) one.
Proof.
  apply (req_trans (sumf cwe_boltzmann_dist)
                   (mult (inv_pos Z Z_pos)
                         (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                   one).
  - exact (sum_linear (inv_pos Z Z_pos)
                      (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))).
  - apply (req_trans (mult (inv_pos Z Z_pos)
                           (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))))
                     (mult (inv_pos Z Z_pos) Z)
                     one).
    + apply (req_mult_compat (inv_pos Z Z_pos) (inv_pos Z Z_pos)
                             (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s)))) Z).
      * apply req_refl.
      * apply (req_sym Z (sumf (fun s => exp_neg (mult (inv_pos D D_pos) (base_loss s))))).
        exact partition_condition.
    + apply (req_trans (mult (inv_pos Z Z_pos) Z) (mult Z (inv_pos Z Z_pos)) one).
      * apply mult_comm.
      * apply inv_pos_correct.
Qed.

(* C. Pointwise decomposition (the req version of the Id original L16198 p_times_energy_decomp) *)
Lemma req_p_times_energy_decomp :
  forall (p : S -> R) (s : S),
    req (mult (p s) (base_loss s)) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos))))).
Proof.
  intros p s.
  assert (HlegA : req (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
  { apply (req_trans (mult (p s) (base_loss s)) (mult (p s) (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))))).
    - apply (req_mult_compat (p s) (p s) (base_loss s) (opp (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
      * apply req_refl.
      * apply (energy_in_log_boltzmann_bridge s).
    - apply (req_mult_opp_l (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). }
  assert (Hswap : req (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
  { apply (req_trans (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult (p s) D) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
    - apply mult_assoc.
      - apply (req_trans (mult (mult (p s) D) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))).
        * apply (req_mult_compat (mult (p s) D) (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))).
          { apply mult_comm. }
          { apply req_refl. }
        * apply (req_sym (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult (mult D (p s)) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))). apply mult_assoc.
  }
  assert (Hdist2 : req (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
  { apply (req_trans (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (plus (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))).
    - apply (req_mult_compat D D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))) (plus (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))) (mult (p s) (log Z Z_pos)))).
      + apply req_refl.
      + apply distrib.
    - apply distrib. }
  apply (req_trans (mult (p s) (base_loss s)) (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
  - exact HlegA.
  - apply (req_trans (opp (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
    + apply (req_opp_compat (mult (p s) (mult D (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))). exact Hswap.
    + apply (req_trans (opp (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos))))) (opp (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))) (plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))) (opp (mult D (mult (p s) (log Z Z_pos)))))).
      * apply (req_opp_compat (mult D (mult (p s) (plus (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)) (log Z Z_pos)))) (plus (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))) (mult D (mult (p s) (log Z Z_pos))))). exact Hdist2.
      * apply req_opp_plus.
Qed.
(* D. The main migration: req_free_energy_kl_decomp *)
(*    F[p] == F[p_b] + D * KL(p||p_b) (the setoid-signature version of the Id original L16259) *)
(*    Notation: lgpb s := log (cwe_boltzmann_dist s) Hpb; lgps s := log (p s) Hp; *)
(*    A := D * sum p * lgpb; B := D * sum p * lgps; DlgZ := D * log Z; *)
(*    KL := fun s => p s * (lgps s - lgpb s); Fpb := cwe_free_energy p_b *)
Theorem req_free_energy_kl_decomp :
  forall (p : S -> R) (Hp : cwe_normalized p) (p0 : cwe_positive_dist p),
    req (cwe_free_energy p p0)
        (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
              (mult D (sumf (fun s =>
                mult (p s) (rminus (log (p s) (p0 s))
                                   (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
Proof.
  intros p Hp p0.
  (* Bridge: F[p_b] == mult (opp D) lgZ == opp (D * lgZ) (the req form of the Id-family step 2) *)
  assert (Hfb' : req (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
                     (opp (mult D (log Z Z_pos)))).
  { apply (req_trans (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive)
                     (mult (opp D) (log Z Z_pos))
                     (opp (mult D (log Z Z_pos)))).
    - exact free_energy_boltzmann_bridge.
    - apply req_opp_mult_l. }
  (* Step 1: sum p*E == opp A + opp DlgZ (the Id original Hse) *)
  assert (Hse : req (sumf (fun s => mult (p s) (base_loss s)))
                    (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                          (opp (mult D (log Z Z_pos))))).
  { apply (req_trans (sumf (fun s => mult (p s) (base_loss s)))
                     (sumf (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                          (opp (mult D (mult (p s) (log Z Z_pos))))))
                     (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (log Z Z_pos))))).
    - apply (sum_ext (fun s => mult (p s) (base_loss s))
                     (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                    (opp (mult D (mult (p s) (log Z Z_pos)))))).
      { intro s. apply req_p_times_energy_decomp. }
    - apply (req_trans (sumf (fun s => plus (opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                            (opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos))))))
                       (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                             (opp (mult D (log Z Z_pos))))).
      { apply sum_add. }
      { apply (req_plus_compat (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                               (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                               (opp (mult D (log Z Z_pos)))).
        - (* sum opp(D*p*lgpb) == opp(D*sum p*lgpb): sum_opp plus D-linearity extraction *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (sumf (fun s => mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
          { apply req_sum_opp. }
          { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                  (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
            { apply (sum_linear D (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))). } }
        - (* sum opp(D*p*lgZ) == opp(D*lgZ): sum_opp plus D-linearity, then the normalization chain sum p*lgZ = lgZ*sum p = lgZ *)
          apply (req_trans (sumf (fun s => opp (mult D (mult (p s) (log Z Z_pos)))))
                           (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                           (opp (mult D (log Z Z_pos)))).
          { apply req_sum_opp. }
          { apply (req_trans (opp (sumf (fun s => mult D (mult (p s) (log Z Z_pos)))))
                             (opp (mult D (sumf (fun s => mult (p s) (log Z Z_pos)))))
                             (opp (mult D (log Z Z_pos)))).
            { apply (req_opp_compat (sumf (fun s => mult D (mult (p s) (log Z Z_pos))))
                                    (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))).
              { apply (sum_linear D (fun s => mult (p s) (log Z Z_pos))). } }
            { apply (req_opp_compat (mult D (sumf (fun s => mult (p s) (log Z Z_pos))))
                                    (mult D (log Z Z_pos))).
              { apply (req_mult_compat D D (sumf (fun s => mult (p s) (log Z Z_pos))) (log Z Z_pos)).
                { apply req_refl. }
                { apply (req_trans (sumf (fun s => mult (p s) (log Z Z_pos)))
                                   (sumf (fun s => mult (log Z Z_pos) (p s)))
                                   (log Z Z_pos)).
                  { apply (sum_ext (fun s => mult (p s) (log Z Z_pos)) (fun s => mult (log Z Z_pos) (p s))).
                    { intro s2. apply mult_comm. } }
                  { apply (req_trans (sumf (fun s => mult (log Z Z_pos) (p s)))
                                     (mult (log Z Z_pos) (sumf p))
                                     (log Z Z_pos)).
                    { apply (sum_linear (log Z Z_pos) p). }
                    { apply (req_trans (mult (log Z Z_pos) (sumf p))
                                       (mult (log Z Z_pos) one)
                                       (log Z Z_pos)).
                      { apply (req_mult_compat (log Z Z_pos) (log Z Z_pos) (sumf p) one).
                        { apply req_refl. }
                        { exact Hp. } }
                      { apply mult_one. } } } } } } }
  }
  }
  (* Step 3: D*KL == B + opp A (the Id original Hkl) *)
  assert (Hkl : req (mult D (sumf (fun s =>
                      mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                    (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                          (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { assert (Hpt2 : forall s : S,
        req (mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
            (plus (mult (p s) (log (p s) (p0 s)))
                  (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
    { intro s. unfold rminus.
      apply (req_trans (mult (p s) (plus (log (p s) (p0 s)) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s))) (mult (p s) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (plus (mult (p s) (log (p s) (p0 s)))
                             (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
      { apply distrib. }
      { apply (req_plus_compat (mult (p s) (log (p s) (p0 s))) (mult (p s) (log (p s) (p0 s)))
                               (mult (p s) (opp (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
                               (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))).
        { apply req_refl. }
        { apply req_mult_opp_l. } } }
    assert (Hinner : req (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply (req_trans (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                       (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                       (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                             (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (sum_ext (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))
                       (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
        { exact Hpt2. } }
      { apply (req_trans (sumf (fun s => plus (mult (p s) (log (p s) (p0 s))) (opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                         (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                               (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
        { apply sum_add. }
        { apply (req_plus_compat (sumf (fun s => mult (p s) (log (p s) (p0 s)))) (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                 (sumf (fun s => opp (mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                                 (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
          { apply req_refl. }
          { apply req_sum_opp. } } } }
    apply (req_trans (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                     (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply (req_mult_compat D D
                             (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))
                             (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply req_refl. }
      { exact Hinner. } }
    apply (req_trans (mult D (plus (sumf (fun s => mult (p s) (log (p s) (p0 s))))
                                   (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))
                     (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { apply distrib. }
    apply (req_plus_compat (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))
                           (mult D (opp (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))
                           (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
    { apply req_refl. }
    { apply req_mult_opp_l. } }

  (* Step 4: the ring-algebra collapse (the Id original Hfin: (opp A + opp DlgZ) + B -> opp DlgZ + (B + opp A)) *)
  assert (Hfin : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                     (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))))).
  { set (A := (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))).
    set (DlgZ := (mult D (log Z Z_pos))).
    set (B := (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    apply (req_trans (plus (plus (opp A) (opp DlgZ)) B)
                     (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_sym (plus (opp A) (plus (opp DlgZ) B))
                     (plus (plus (opp A) (opp DlgZ)) B)).
      apply plus_assoc. }
    apply (req_trans (plus (opp A) (plus (opp DlgZ) B))
                     (plus (opp A) (plus B (opp DlgZ)))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (opp A) (opp A) (plus (opp DlgZ) B) (plus B (opp DlgZ))).
      { apply req_refl. }
      { apply plus_comm. } }
    apply (req_trans (plus (opp A) (plus B (opp DlgZ)))
                     (plus (plus (opp A) B) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply plus_assoc. }
    apply (req_trans (plus (plus (opp A) B) (opp DlgZ))
                     (plus (plus B (opp A)) (opp DlgZ))
                     (plus (opp DlgZ) (plus B (opp A)))).
    { apply (req_plus_compat (plus (opp A) B) (plus B (opp A)) (opp DlgZ) (opp DlgZ)).
      { apply plus_comm. }
      { apply req_refl. } }
    apply plus_comm. }
  (* Assembly: Hleg1 (the conversion of the definitional unfolding of cwe_free_energy p, with Hse in the compat slot); Hleg2 (Hfin with the reverse finishing slots Hfb'/Hkl) *)
  assert (Hleg1 : req (cwe_free_energy p p0) (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))).
  { unfold cwe_free_energy.
    apply (req_plus_compat (sumf (fun s => mult (p s) (base_loss s))) (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))).
    { exact Hse. }
    { apply req_refl. } }
  assert (Hleg2 : req (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s)))))) (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
  { apply (req_trans (plus (plus (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (opp (mult D (log Z Z_pos)))) (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))))
                      (plus (opp (mult D (log Z Z_pos))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))))
                      (plus (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))).
    { exact Hfin. }
    { apply (req_plus_compat (opp (mult D (log Z Z_pos))) (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))) (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s))))))).
      { apply (req_sym (cwe_free_energy cwe_boltzmann_dist req_boltzmann_positive) (opp (mult D (log Z Z_pos)))). exact Hfb'. }
      { apply (req_sym (mult D (sumf (fun s => mult (p s) (rminus (log (p s) (p0 s)) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))) (plus (mult D (sumf (fun s => mult (p s) (log (p s) (p0 s))))) (opp (mult D (sumf (fun s => mult (p s) (log (cwe_boltzmann_dist s) (req_boltzmann_positive s)))))))). exact Hkl. } } }
  exact (req_trans _ _ _ Hleg1 Hleg2).
Qed.

End ReqFreeEnergyPilot.

(* Pilot 2 (best effort): req_attention_is_gibbs_temp *)
(*   Id original: CW L28634 (the AttentionGibbsBridge section, L27929-28710). *)
(*   Three premises and the pointwise conclusion migrate to req; the in-section infrastructure (exp_pos_fn / *)
(*   partition_function_temp / softmax_temp / boltzmann_factor /  *)
(*   Z_thermo / boltzmann_dist_attn) is rebuilt by same-shape definitions. *)
(*   An interface gap was found: RealInterfaceEnhancedSetoid has no exp_neg-compatible *)
(*   field (free in the Id family through id_cong); a req-signature bridge premise position *)
(*   carries it -- the Real instance satisfies it through cauchy_real_exp_wd (the L40440 precedent). *)
Section ReqGibbsPilot.
Variable S : Set.
Variable sumf : (S -> R) -> R.
Hypothesis sum_pos : forall f : S -> R, (forall s : S, lt zero (f s)) -> lt zero (sumf f).
(* The interface-gap bridge: the req compatibility of exp_neg (missing field, see the note above) *)
Hypothesis req_exp_neg_ext : forall x y : R, req x y -> req (exp_neg x) (exp_neg y).

Variable T : R.
Variable T_pos : lt zero T.
Variable D : R.
Variable D_pos : lt zero D.
Variable energy : S -> R.
Variable z : S -> R.

Definition cwe_exp_pos_fn (x : R) : R := exp_neg (opp x).
Definition cwe_partition_function_temp : R :=
  sumf (fun s => cwe_exp_pos_fn (mult (inv_pos T T_pos) (z s))).
Hypothesis partition_function_temp_pos : lt zero cwe_partition_function_temp.
Definition cwe_softmax_temp (s : S) : R :=
  mult (cwe_exp_pos_fn (mult (inv_pos T T_pos) (z s)))
       (inv_pos cwe_partition_function_temp partition_function_temp_pos).
Definition boltzmann_factor (s : S) : R :=
  exp_neg (mult (inv_pos D D_pos) (energy s)).
Definition Z_thermo : R := sumf boltzmann_factor.
Variable Z_thermo_pos : lt zero Z_thermo.
Definition boltzmann_dist_attn (s : S) : R :=
  mult (inv_pos Z_thermo Z_thermo_pos) (boltzmann_factor s).

Theorem req_attention_is_gibbs_temp :
  (req (inv_pos T T_pos) (inv_pos D D_pos)) ->
  (forall s : S, req (energy s) (opp (z s))) ->
  (req Z_thermo cwe_partition_function_temp) ->
  forall s : S, req (cwe_softmax_temp s) (boltzmann_dist_attn s).
Proof.
  intros HD Henergy HZ s.
  assert (Hf : req (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                   (exp_neg (mult (inv_pos D D_pos) (energy s)))).
  { apply (req_exp_neg_ext (opp (mult (inv_pos T T_pos) (z s)))
                           (mult (inv_pos D D_pos) (energy s))).
    apply (req_trans (opp (mult (inv_pos T T_pos) (z s)))
                     (mult (inv_pos T T_pos) (opp (z s)))
                     (mult (inv_pos D D_pos) (energy s))).
    - exact (req_sym (mult (inv_pos T T_pos) (opp (z s)))
                     (opp (mult (inv_pos T T_pos) (z s)))
                     (req_mult_opp_l (inv_pos T T_pos) (z s))).
    - apply (req_mult_compat (inv_pos T T_pos) (inv_pos D D_pos) (opp (z s)) (energy s)).
      + exact HD.
      + apply (req_sym (energy s) (opp (z s))). apply Henergy. }
  assert (Hie : req (inv_pos Z_thermo Z_thermo_pos)
                    (inv_pos cwe_partition_function_temp partition_function_temp_pos)).
  { apply (inv_pos_ext Z_thermo cwe_partition_function_temp
                       Z_thermo_pos partition_function_temp_pos HZ). }
  unfold cwe_softmax_temp, boltzmann_dist_attn, boltzmann_factor, cwe_exp_pos_fn.
  apply (req_trans (mult (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (inv_pos cwe_partition_function_temp partition_function_temp_pos))
                       (mult (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos Z_thermo Z_thermo_pos))
                       (mult (inv_pos Z_thermo Z_thermo_pos)
                             (exp_neg (mult (inv_pos D D_pos) (energy s))))).
    { apply (req_mult_compat (exp_neg (opp (mult (inv_pos T T_pos) (z s))))
                             (exp_neg (mult (inv_pos D D_pos) (energy s)))
                             (inv_pos cwe_partition_function_temp partition_function_temp_pos)
                             (inv_pos Z_thermo Z_thermo_pos)).
      { exact Hf. }
      { apply (req_sym (inv_pos Z_thermo Z_thermo_pos) (inv_pos cwe_partition_function_temp partition_function_temp_pos)). exact Hie. } }
    apply mult_comm.
Qed.

End ReqGibbsPilot.
End SigMigrate.

(* ---------- UpBudgetReal ---------- *)
Module BudgetReal.
From Stdlib Require Import QArith.QArith QArith.Qabs.
Set Extraction Output Directory ".".
(*  -- the Real-layer explicit iteration budget theorem for geometric breakdown *)
(* The Real-layer carrier of the explicit iteration budget, the main contribution of paper 4 (gradient dynamics convergence): *)
(* the interface premise of the root ConvergenceCauchy section *)
(*   r_arch_pow : 0 < a -> 0 < eps -> sigT (fun n => a * kappa^n < eps) *)
(* so far lived only as an interface assumption; this file closes the gap over the concrete Cauchy reals (the *)
(* Real := sigT (fun u : Qseq => cauchy u) of CW_ConstructiveWorld_219): *)
(* Main result r_arch_pow_real: *)
(*   for all kappa, a, eps with 0 < kappa < 1, 0 < a, 0 < eps, an explicit nat witness N exists with *)
(*   a * kappa^N < eps. *)
(* Construction route (route A, purely at the Real layer, no detour through Q): *)
(*   set i := 1/kappa > 1 and c := i - 1 > 0. The Bernoulli inequality *)
(*   i^N >= 1 + (N#1)*c gives the power lower bound; the budget real y := (a/eps)/c, through *)
(*   real_arch (the Real-layer Archimedean property, proved in the 217 root), solves for N; *)
(*   the reciprocal contravariance (real_inv_pos_lt_contra) and the pow/inv identity *)
(*   then connect back to a * kappa^N < eps. The explicit form of N: the nat delivered by real_arch. *)
(* Item 1: sufficiency of the budget condition (the log closed-form condition) *)
(*   r_pow_log_form      log(kappa^N) == (N#1)*log kappa (by induction) *)
(*   log_kappa_neg       0 < kappa < 1 gives -log kappa > 0 (the hlogz_strict proof) *)
(*   budget_cond_sufficient  N*|log kappa| > log a - log eps gives a*kappa^N < eps *)
(*   (through the strict monotonicity cauchy_real_exp_mono and the cw_log_exp_right inversion) *)
(* Item 3: the tail-bound shape of theorem 4.10 of paper 4 (pure order algebra) *)
(*   real_pow_anti_mono  p ≤ q ⟹ κ^q ≤ κ^p                        *)
(*   geo_tail_budget     N <= min m n and a*kappa^N < eps give a*kappa^(min) < eps *)
(*   budget_min_tail     existence of the budget N composed with the min tail bound *)
(* Discipline: purely constructive (zero occurrences of the banned lexicon; see technical report G1); *)
(*       Set-level statements (real_lt/real_le/real_eq/sigT/And); *)
(*       closed by Qed throughout; machines already proved in the root are reused, not re-proved. *)


Local Open Scope Q_scope.

(* ============ 0. Powers of concrete reals (the Real-layer r_pow) ============ *)

Fixpoint real_pow (x : Real) (n : nat) : Real :=
  match n with
  | O => real_one
  | Datatypes.S m => real_mult x (real_pow x m)
  end.

(* The interface named as in the original task statement: r_pow kappa N is real_pow kappa N *)
Abbreviation r_pow := real_pow.

(* Compatibility of powers with real_eq *)
Lemma real_pow_eq_compat : forall (x y : Real) (n : nat),
  real_eq x y -> real_eq (real_pow x n) (real_pow y n).
Proof.
  intros x y n Hxy. induction n as [| m IH].
  - apply real_eq_refl.
  - cbn [real_pow].
    apply (RealSetoid.real_eq_mult_compat x (real_pow x m) y (real_pow y m)).
    + exact Hxy.
    + exact IH.
Qed.

(* Positivity of powers: 0 < x gives 0 < x^n *)
Lemma cwe_real_pow_pos : forall (x : Real) (n : nat),
  real_lt real_zero x -> real_lt real_zero (real_pow x n).
Proof.
  intros x n Hx. induction n as [| m IH].
  - exact real_lt_zero_one.
  - cbn [real_pow]. exact (real_mult_pos_compat x (real_pow x m) Hx IH).
Qed.

(* ============ 1. Elementary algebra utilities (filling the gaps left in the 217 root) ============ *)

(* 0#1 == 0 (the nat embedding of zero) *)
Lemma real_const_zero_thm : real_eq (real_const (Z.of_nat 0 # 1)) real_zero.
Proof.
  apply real_eq_of_zero_diff.
  intro n.
  change (projT1 (real_const (Z.of_nat 0 # 1)) n) with 0%Q.
  change (projT1 real_zero n) with 0%Q.
  apply qeq_imp_qeqT. ring.
Qed.

(* 1*x == x (the root real_mult_one has the x*1 shape) *)
Lemma real_mult_one_l : forall x : Real, real_eq (real_mult real_one x) x.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_one)).
  - apply real_mult_comm.
  - apply real_mult_one.
Qed.

(* 0*x == 0 (the root real_mult_zero has the x*0 shape) *)
Lemma real_mult_zero_l : forall x : Real, real_eq (real_mult real_zero x) real_zero.
Proof.
  intro x.
  apply (real_eq_trans _ (real_mult x real_zero)).
  - apply real_mult_comm.
  - apply real_mult_zero.
Qed.

(* The multiplicative successor of the nat embedding: (S n)#1*x == (n#1)*x + x *)
Lemma real_nat_mult_succ : forall (n : nat) (x : Real),
  real_eq (real_mult (real_const (Z.of_nat (Datatypes.S n) # 1)) x)
          (real_plus (real_mult (real_const (Z.of_nat n # 1)) x) x).
Proof.
  intros n x.
  apply (real_eq_trans _ (real_mult (real_plus (real_const (Z.of_nat n # 1)) real_one) x)).
  - apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat (Datatypes.S n) # 1)) x
                                          (real_plus (real_const (Z.of_nat n # 1)) real_one) x).
    + apply b4_lift_succ.
    + apply real_eq_refl.
  - apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat n # 1)) x)
                                      (real_mult real_one x))).
    + apply (real_eq_sym _ _ (real_distrib_r_local (real_const (Z.of_nat n # 1)) real_one x)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (real_const (Z.of_nat n # 1)) x)
                                            (real_mult real_one x)
                                            (real_mult (real_const (Z.of_nat n # 1)) x) x).
      * apply real_eq_refl.
      * apply real_mult_one_l.
Qed.

(* Inverse uniqueness, supplement: inv 1 == 1 (already available in the root as real_inv_one_local, used directly) *)
(* (not re-proved here; see real_inv_one_local) *)

(* Dedicated to reciprocal positivity: the bridge to 1 < 1/kappa (real_inv_pos_lt_contra plus inv 1 == 1) *)

(* ============ 2. The power/inverse identity (kappa^N * (1/kappa)^N == 1) ============ *)

Lemma real_pow_inv_pair : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_mult (real_pow k n) (real_pow (real_inv_pos k Hk) n)) real_one.
Proof.
  intros k Hk n. induction n as [| m IH].
  - cbn [real_pow]. apply real_mult_one.
  - cbn [real_pow].
    (* (k*k^m)*(i*i^m) == 1 where i := 1/kappa *)
    apply (real_eq_trans _ (real_mult (real_mult (real_pow k m) k)
                                      (real_mult (real_inv_pos k Hk)
                                                 (real_pow (real_inv_pos k Hk) m)))).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult k (real_pow k m))
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))
               (real_mult (real_pow k m) k)
               (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m))).
      * apply real_mult_comm.
      * apply real_eq_refl.
    + apply (real_eq_trans _ (real_mult (real_pow k m)
                                        (real_mult k (real_mult (real_inv_pos k Hk)
                                                                (real_pow (real_inv_pos k Hk) m))))).
      * apply (real_eq_sym _ _ (real_mult_assoc (real_pow k m) k
                         (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))).
      * apply (real_eq_trans _ (real_mult (real_pow k m)
                                          (real_mult (real_mult k (real_inv_pos k Hk))
                                                     (real_pow (real_inv_pos k Hk) m)))).
        -- apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                   (real_mult k (real_mult (real_inv_pos k Hk) (real_pow (real_inv_pos k Hk) m)))
                   (real_pow k m)
                   (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))).
           ++ apply real_eq_refl.
           ++ apply (real_mult_assoc k (real_inv_pos k Hk)
                                        (real_pow (real_inv_pos k Hk) m)).
        -- apply (real_eq_trans _ (real_mult (real_pow k m)
                                             (real_mult real_one (real_pow (real_inv_pos k Hk) m)))).
           ++ apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                      (real_mult (real_mult k (real_inv_pos k Hk)) (real_pow (real_inv_pos k Hk) m))
                      (real_pow k m)
                      (real_mult real_one (real_pow (real_inv_pos k Hk) m))).
              ** apply real_eq_refl.
              ** apply (RealSetoid.real_eq_mult_compat (real_mult k (real_inv_pos k Hk))
                          (real_pow (real_inv_pos k Hk) m) real_one (real_pow (real_inv_pos k Hk) m)).
                 --- exact (real_inv_pos_correct k Hk).
                 --- apply real_eq_refl.
           ++ apply (real_eq_trans _ (real_mult (real_pow k m)
                                                (real_pow (real_inv_pos k Hk) m))).
              ** apply (RealSetoid.real_eq_mult_compat (real_pow k m)
                          (real_mult real_one (real_pow (real_inv_pos k Hk) m))
                          (real_pow k m) (real_pow (real_inv_pos k Hk) m)).
                 --- apply real_eq_refl.
                 --- apply real_mult_one_l.
              ** exact IH.
Qed.

(* ============ 3. le/lt helpers (1 <= 1+x, 0 <= (n#1)*x, y < 1+y) ============ *)

Lemma cwe_real_le_one_plus : forall x : Real,
  real_le real_zero x -> real_le real_one (real_plus real_one x).
Proof.
  intros x Hx.
  apply (real_le_trans _ (real_plus real_one real_zero)).
  - apply real_eq_le_bridge.
    apply (real_eq_sym _ _ (real_plus_zero real_one)).
  - exact (real_le_plus_compat real_one real_one real_zero x (real_le_refl real_one) Hx).
Qed.

Lemma real_lt_plus_one : forall y : Real, real_lt y (real_plus real_one y).
Proof.
  intro y.
  apply (real_eq_lt_lt y (real_plus real_zero y) (real_plus real_one y)).
  - exact (real_eq_sym (real_plus real_zero y) y (sf_real_plus_zero_l y)).
  - exact (real_lt_plus_compat_lt_le real_zero real_one y y real_lt_zero_one (real_le_refl y)).
Qed.

(* Nonnegativity of (n#1)*x: 0 < x gives 0 <= (n#1)*x (nat-embedded multiples are nonnegative) *)
Lemma real_nat_mult_nonneg : forall (n : nat) (x : Real),
  real_lt real_zero x -> real_le real_zero (real_mult (real_const (Z.of_nat n # 1)) x).
Proof.
  intros n x Hx. induction n as [| m IH].
  - apply real_eq_le_bridge.
    apply (real_eq_trans _ (real_mult real_zero x)).
    + apply (real_eq_sym _ _ (real_mult_zero_l x)).
    + apply (RealSetoid.real_eq_mult_compat real_zero x (real_const (Z.of_nat 0 # 1)) x).
      * apply (real_eq_sym _ _ real_const_zero_thm).
      * apply real_eq_refl.
  - apply real_lt_le_bridge.
    apply (real_lt_eq_lt _ (real_plus (real_mult (real_const (Z.of_nat m # 1)) x) x)).
    + apply (real_lt_eq_lt _ (real_plus x (real_mult (real_const (Z.of_nat m # 1)) x))).
      * apply (real_eq_lt_lt real_zero (real_plus real_zero real_zero)).
        -- exact (real_eq_sym _ _ (real_plus_zero real_zero)).
        -- exact (real_lt_plus_compat_lt_le real_zero x real_zero
                    (real_mult (real_const (Z.of_nat m # 1)) x) Hx IH).
      * apply real_plus_comm.
    + apply (real_eq_sym _ _ (real_nat_mult_succ m x)).
Qed.

(* ============ 4. The Bernoulli power lower bound: (1+c)^n >= 1 + (n#1)*c for c > 0 ============ *)

Lemma bernoulli_pow : forall (c : Real) (Hc : real_lt real_zero c) (n : nat),
  real_le (real_plus real_one (real_mult (real_const (Z.of_nat n # 1)) c))
          (real_pow (real_plus real_one c) n).
Proof.
  intros c Hc n. induction n as [| m IH].
  - cbn [real_pow].
    apply (real_le_trans _ real_one).
    + apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one real_zero)).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat 0 # 1)) c) real_one real_zero).
        -- apply real_eq_refl.
        -- apply (real_eq_trans _ (real_mult real_zero c)).
           ++ apply (RealSetoid.real_eq_mult_compat (real_const (Z.of_nat 0 # 1)) c
                       real_zero c).
              ** exact real_const_zero_thm.
              ** apply real_eq_refl.
           ++ apply (real_mult_zero_l c).
      * exact (real_plus_zero real_one).
    + apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_plus (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c)) c)).
    + (* 1 + (S m)#1*c == (1 + m#1*c) + c *)
      apply real_eq_le_bridge.
      apply (real_eq_trans _ (real_plus real_one (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c))).
      * apply (RealSetoid.real_eq_plus_compat real_one
                 (real_mult (real_const (Z.of_nat (Datatypes.S m) # 1)) c)
                 real_one
                 (real_plus (real_mult (real_const (Z.of_nat m # 1)) c) c)).
        -- apply real_eq_refl.
        -- apply (real_nat_mult_succ m c).
      * apply real_plus_assoc.
    + (* (1 + m#1*c) + c <= (1+c)*(1+c)^m *)
      apply (real_le_trans _ (real_plus (real_pow (real_plus real_one c) m)
                                        (real_mult c (real_pow (real_plus real_one c) m)))).
      * assert (Hx0 : real_le real_zero (real_mult (real_const (Z.of_nat m # 1)) c))
          by exact (real_nat_mult_nonneg m c Hc).
        assert (H1P : real_le real_one (real_pow (real_plus real_one c) m)).
        { apply (real_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat m # 1)) c))).
          - exact (cwe_real_le_one_plus _ Hx0).
          - exact IH. }
        apply (real_le_plus_compat _ _ _ _ IH).
        (* c <= c*(1+c)^m *)
        apply (real_le_trans _ (real_mult c real_one)).
        -- apply real_eq_le_bridge.
           apply (real_eq_sym _ _ (real_mult_one c)).
        -- apply (real_le_trans _ (real_mult real_one c)).
           ++ apply real_eq_le_bridge.
              exact (real_mult_comm c real_one).
           ++ apply (real_le_trans _ (real_mult (real_pow (real_plus real_one c) m) c)).
              ** exact (real_le_mult_compat real_one (real_pow (real_plus real_one c) m) c Hc H1P).
              ** apply real_eq_le_bridge.
                 exact (real_mult_comm (real_pow (real_plus real_one c) m) c).
      * (* P + c*P == (1+c)*P *)
        apply real_eq_le_bridge.
        apply (real_eq_trans _ (real_plus (real_mult real_one (real_pow (real_plus real_one c) m))
                                          (real_mult c (real_pow (real_plus real_one c) m)))).
        -- apply (RealSetoid.real_eq_plus_compat (real_pow (real_plus real_one c) m)
                    (real_mult c (real_pow (real_plus real_one c) m))
                    (real_mult real_one (real_pow (real_plus real_one c) m))
                    (real_mult c (real_pow (real_plus real_one c) m))).
           ++ apply (real_eq_sym _ _ (real_mult_one_l (real_pow (real_plus real_one c) m))).
           ++ apply real_eq_refl.
        -- exact (real_distrib_r_local real_one c (real_pow (real_plus real_one c) m)).
Qed.


(* ============ 5. Item 2, main theorem: the Real-layer explicit nat budget of geometric breakdown ============ *)
(*   The explicit form of N: the nat that real_arch solves for on the budget real y := (a/eps)/(1/kappa - 1). *)

Theorem r_arch_pow_real :
  forall (kappa : Real) (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (a : Real) (Ha : real_lt real_zero a) (eps : Real) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => real_lt (real_mult a (r_pow kappa N)) eps).
Proof.
  intros kappa Hk1 Hk2 a Ha eps Heps.
  assert (Hinvpos : real_lt real_zero (real_inv_pos kappa Hk1))
    by exact (real_inv_pos_pos kappa Hk1).
  assert (HoneLtInv : real_lt real_one (real_inv_pos kappa Hk1)).
  { apply (real_eq_lt_lt real_one (real_inv_pos real_one real_lt_zero_one)
                         (real_inv_pos kappa Hk1)).
    - apply (real_eq_sym _ _ real_inv_one_local).
    - exact (real_inv_pos_lt_contra kappa real_one Hk1 real_lt_zero_one Hk2). }
  assert (Hc : real_lt real_zero (real_plus (real_inv_pos kappa Hk1) (real_opp real_one)))
    by exact (real_lt_opp_plus real_one (real_inv_pos kappa Hk1) HoneLtInv).
  assert (Hax : real_lt real_zero (real_mult a (real_inv_pos eps Heps)))
    by exact (real_mult_pos_compat a (real_inv_pos eps Heps) Ha (real_inv_pos_pos eps Heps)).
  set (c := real_plus (real_inv_pos kappa Hk1) (real_opp real_one)) in Hc |- *.
  set (x := real_mult a (real_inv_pos eps Heps)) in Hax |- *.
  assert (Hyc : real_lt real_zero (real_mult x (real_inv_pos c Hc)))
    by exact (real_mult_pos_compat x (real_inv_pos c Hc) Hax (real_inv_pos_pos c Hc)).
  destruct (real_arch (real_mult x (real_inv_pos c Hc))) as [N [HN2 HN]].
  (* x < (N#1)*c: the reshaped real_mult_div gives (x*(1/c))*c == x, then multiplying by c preserves the order *)
  assert (Hxc_lt : real_lt x (real_mult (real_const (Z.of_nat N # 1)) c)).
  { apply (real_eq_lt_lt x (real_mult (real_mult x (real_inv_pos c Hc)) c)).
    - apply (real_eq_trans _ (real_mult c (real_mult x (real_inv_pos c Hc)))).
      + apply (real_eq_sym _ _ (real_mult_div c x Hc)).
      + apply real_mult_comm.
    - exact (real_mult_lt_compat (real_mult x (real_inv_pos c Hc))
               (real_const (Z.of_nat N # 1)) c HN Hc). }
  (* 1 + c == 1/κ *)
  assert (Honec : real_eq (real_plus real_one c) (real_inv_pos kappa Hk1)).
  { unfold c. apply (real_eq_trans _ (real_plus (real_plus real_one (real_inv_pos kappa Hk1))
                                                (real_opp real_one))).
    - apply real_plus_assoc.
    - apply (real_eq_trans _ (real_plus (real_plus (real_inv_pos kappa Hk1) real_one)
                                        (real_opp real_one))).
      + apply (RealSetoid.real_eq_plus_compat
                 (real_plus real_one (real_inv_pos kappa Hk1)) (real_opp real_one)
                 (real_plus (real_inv_pos kappa Hk1) real_one) (real_opp real_one)).
        * apply real_plus_comm.
        * apply real_eq_refl.
      + apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1)
                                          (real_plus real_one (real_opp real_one)))).
        * apply (real_eq_sym _ _ (real_plus_assoc (real_inv_pos kappa Hk1) real_one
                                                    (real_opp real_one))).
        * apply (real_eq_trans _ (real_plus (real_inv_pos kappa Hk1) real_zero)).
          -- apply (RealSetoid.real_eq_plus_compat (real_inv_pos kappa Hk1)
                      (real_plus real_one (real_opp real_one))
                      (real_inv_pos kappa Hk1) real_zero).
             ++ apply real_eq_refl.
             ++ apply real_plus_opp.
          -- apply (real_plus_zero (real_inv_pos kappa Hk1)). }
  (* x < 1 + (N#1)*c <= (1+c)^N == (1/kappa)^N (the Bernoulli le plus the strict part above) *)
  assert (Hkey : real_lt x (real_pow (real_inv_pos kappa Hk1) N)).
  { apply (real_lt_eq_lt _ (real_pow (real_plus real_one c) N)).
    - apply (real_lt_le_trans _ (real_plus real_one (real_mult (real_const (Z.of_nat N # 1)) c))).
      + apply (real_lt_trans _ (real_mult (real_const (Z.of_nat N # 1)) c)).
        * exact Hxc_lt.
        * exact (real_lt_plus_one _).
      + exact (bernoulli_pow c Hc N).
    - apply (real_pow_eq_compat _ _ N Honec). }
  (* kappa^N == 1/(1/kappa)^N (the pow/inv identity plus uniqueness of inverses) *)
  assert (HposN : real_lt real_zero (real_pow (real_inv_pos kappa Hk1) N))
    by exact (cwe_real_pow_pos _ N Hinvpos).
  assert (Hpowinv : real_eq (real_pow kappa N)
                            (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
  { apply (real_inv_unique (real_pow (real_inv_pos kappa Hk1) N) (real_pow kappa N)
                           (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - apply (real_eq_trans _ (real_mult (real_pow kappa N)
                                        (real_pow (real_inv_pos kappa Hk1) N))).
      + apply real_mult_comm.
      + exact (real_pow_inv_pair kappa Hk1 N).
    - exact (real_inv_pos_correct (real_pow (real_inv_pos kappa Hk1) N) HposN). }
  (* 1/x == eps*(1/a) (real_inv_unique applied to x*(eps*(1/a)) == 1) *)
  assert (Hinva : real_eq (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_inv_unique x (real_inv_pos x Hax) (real_mult eps (real_inv_pos a Ha))).
    - exact (real_inv_pos_correct x Hax).
    - apply (real_eq_trans _ (real_mult a
                 (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha))))).
      + apply (real_eq_sym _ _ (real_mult_assoc a (real_inv_pos eps Heps)
                                  (real_mult eps (real_inv_pos a Ha)))).
      + apply (real_eq_trans _ (real_mult a
                 (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)))).
        * apply (RealSetoid.real_eq_mult_compat a
                    (real_mult (real_inv_pos eps Heps) (real_mult eps (real_inv_pos a Ha)))
                    a
                    (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))).
          -- apply real_eq_refl.
          -- apply (real_mult_assoc (real_inv_pos eps Heps) eps
                                                       (real_inv_pos a Ha)).
        * apply (real_eq_trans _ (real_mult a (real_mult real_one (real_inv_pos a Ha)))).
          -- apply (RealSetoid.real_eq_mult_compat a
                      (real_mult (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha))
                      a
                      (real_mult real_one (real_inv_pos a Ha))).
             ++ apply real_eq_refl.
             ++ apply (RealSetoid.real_eq_mult_compat
                          (real_mult (real_inv_pos eps Heps) eps) (real_inv_pos a Ha)
                          real_one (real_inv_pos a Ha)).
                ** apply (real_eq_trans _ (real_mult eps (real_inv_pos eps Heps))).
                   --- apply real_mult_comm.
                   --- exact (real_inv_pos_correct eps Heps).
                ** apply real_eq_refl.
          -- apply (real_eq_trans _ (real_mult a (real_inv_pos a Ha))).
             ++ apply (RealSetoid.real_eq_mult_compat a
                         (real_mult real_one (real_inv_pos a Ha)) a (real_inv_pos a Ha)).
                ** apply real_eq_refl.
                ** apply real_mult_one_l.
             ++ exact (real_inv_pos_correct a Ha). }
  assert (Hinvlt : real_lt (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)
                           (real_inv_pos x Hax)).
  { exact (real_inv_pos_lt_contra x (real_pow (real_inv_pos kappa Hk1) N) Hax HposN Hkey). }
  (* kappa^N < eps*(1/a) *)
  assert (Hklt : real_lt (real_pow kappa N) (real_mult eps (real_inv_pos a Ha))).
  { apply (real_eq_lt_lt _ (real_inv_pos (real_pow (real_inv_pos kappa Hk1) N) HposN)).
    - exact Hpowinv.
    - exact (real_lt_eq_lt _ _ _ Hinvlt Hinva). }
  exists N.
  apply (real_lt_eq_lt (real_mult a (real_pow kappa N))
                       (real_mult a (real_mult eps (real_inv_pos a Ha)))).
  - exact (real_mult_lt_compat_l (real_pow kappa N)
             (real_mult eps (real_inv_pos a Ha)) a Hklt Ha).
  - exact (real_mult_div a eps Ha).
Qed.

(* ============ 6. Item 1: the log-form closed condition (Real layer) ============ *)

(* -log kappa > 0: 0 < kappa < 1 gives log kappa < 0 (the G01_CoreMicro.hlogz_strict proof), then contravariance through opp *)
Lemma log_kappa_neg : forall (kappa : Real)
                         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one),
  real_lt real_zero (real_opp (real_log kappa Hk1)).
Proof.
  intros kappa Hk1 Hk2.
  assert (Hneg : real_lt (real_log kappa Hk1) real_zero)
    by exact (hlogz_strict kappa Hk1 Hk2).
  apply (real_eq_lt_lt real_zero (real_opp real_zero) (real_opp (real_log kappa Hk1))).
  - apply (real_eq_sym _ _ real_opp_zero).
  - exact (real_opp_lt_compat (real_log kappa Hk1) real_zero Hneg).
Qed.

(* The log power identity: log(kappa^N) == (N#1)*log kappa (induction on real_log_mult) *)
Lemma real_pow_log_form : forall (k : Real) (Hk : real_lt real_zero k) (n : nat),
  real_eq (real_log (real_pow k n) (cwe_real_pow_pos k n Hk))
          (real_mult (real_const (Z.of_nat n # 1)) (real_log k Hk)).
Proof.
  intros k Hk n. induction n as [| m IH].
  - apply (real_eq_trans _ real_zero).
    + apply real_log_one.
    + exact (real_eq_sym (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk)) real_zero
               (real_eq_trans (real_mult (real_const (Z.of_nat 0 # 1)) (real_log k Hk))
                              (real_mult real_zero (real_log k Hk)) real_zero
                              (RealSetoid.real_eq_mult_compat
                                 (real_const (Z.of_nat 0 # 1)) (real_log k Hk)
                                 real_zero (real_log k Hk)
                                 real_const_zero_thm (real_eq_refl (real_log k Hk)))
                              (real_mult_zero_l (real_log k Hk)))).
  - cbn [real_pow].
    apply (real_eq_trans _ (real_plus (real_log k Hk)
                                      (real_log (real_pow k m) (cwe_real_pow_pos k m Hk)))).
    + exact (log_inv_mult_thm k (real_pow k m) Hk (cwe_real_pow_pos k m Hk)
               (cwe_real_pow_pos k (Datatypes.S m) Hk)).
    + apply (real_eq_trans _ (real_plus (real_log k Hk)
                   (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk)))).
      * apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) IH).
      * apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                            (real_log k Hk))).
        -- apply (real_plus_comm (real_log k Hk)
                    (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))).
        -- apply (real_eq_trans _ (real_plus (real_mult (real_const (Z.of_nat m # 1))
                                                        (real_log k Hk))
                                             (real_log k Hk))).
           ++ apply (RealSetoid.real_eq_plus_compat
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)
                       (real_mult (real_const (Z.of_nat m # 1)) (real_log k Hk))
                       (real_log k Hk)).
              ** apply real_eq_refl.
              ** apply real_eq_refl.
           ++ apply (real_eq_sym _ _ (real_nat_mult_succ m (real_log k Hk))).
Qed.

(* Item 1, main piece: sufficiency of the budget condition.
   N*|log kappa| > log a - log eps gives a*kappa^N < eps
   (through the log polynomial identity, the strict monotonicity cauchy_real_exp_mono, and the cw_log_exp_right inversion) *)
Theorem budget_cond_sufficient :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (N : nat),
  real_lt (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
          (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1))) ->
  real_lt (real_mult a (real_pow kappa N)) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps N Hcond.

  (* log(a*kappa^N) == log a + N#1*log kappa *)
  assert (Hlogpow : real_eq (real_log (real_mult a (real_pow kappa N))
                                      (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))
                            (real_plus (real_log a Ha)
                                       (real_mult (real_const (Z.of_nat N # 1))
                                                  (real_log kappa Hk1)))).
  { apply (real_eq_trans _ (real_plus (real_log a Ha)
                                      (real_log (real_pow kappa N) (cwe_real_pow_pos kappa N Hk1)))).
    - exact (real_log_mult a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)).
    - apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _)
               (real_pow_log_form kappa Hk1 N)). }
  (* N#1*log kappa == -(N#1*(-log kappa)) *)
  assert (Hnegm : real_eq (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1))
                          (real_opp (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1))))).
  { apply (real_eq_trans _ (real_mult (real_const (Z.of_nat N # 1))
                                      (real_opp (real_opp (real_log kappa Hk1))))).
    - apply (RealSetoid.real_eq_mult_compat _ _ _ _ (real_eq_refl _)
               (real_eq_sym _ _ (real_opp_opp (real_log kappa Hk1)))).
    - apply real_mult_opp_l. }
  (* The condition reshaped: log a < N#1*(-log kappa) + log eps
     (log eps added to both sides of Hcond: La + -Le < W gives (La + -Le) + Le < W + Le) *)
  assert (Hmid : real_lt (real_log a Ha)
                         (real_plus (real_mult (real_const (Z.of_nat N # 1))
                                               (real_opp (real_log kappa Hk1)))
                                    (real_log eps Heps))).
  { apply (real_eq_lt_lt (real_log a Ha)
            (real_plus (real_plus (real_log a Ha) (real_opp (real_log eps Heps)))
                       (real_log eps Heps))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps)))).
      + apply (real_eq_sym _ _).
        apply (real_eq_trans _ (real_plus (real_log a Ha) real_zero)).
        * apply (RealSetoid.real_eq_plus_compat (real_log a Ha)
                   (real_plus (real_opp (real_log eps Heps)) (real_log eps Heps))
                   (real_log a Ha) real_zero).
          -- apply real_eq_refl.
          -- exact (real_eq_trans _ _ _
                     (real_plus_comm (real_opp (real_log eps Heps)) (real_log eps Heps))
                     (real_plus_opp (real_log eps Heps))).
        * apply (real_plus_zero (real_log a Ha)).
      + apply (real_plus_assoc (real_log a Ha) (real_opp (real_log eps Heps))
                                 (real_log eps Heps)).
    - exact (real_lt_plus_compat_lt_le _ _ _ _ Hcond (real_le_refl (real_log eps Heps))). }
  (* Additive cancellation: x == La - W and La < W + Le give x < Le (a purely additive lemma dedicated to item 1) *)
  assert (Hshift : forall (x La Le W : Real),
            real_eq x (real_plus La (real_opp W)) ->
            real_lt La (real_plus W Le) ->
            real_lt x Le).
  { intros x0 La0 Le0 W0 H1 H2.
    apply (real_eq_lt_lt x0 (real_plus La0 (real_opp W0))).
    - exact H1.
    - apply (real_lt_eq_lt _ (real_plus (real_plus W0 Le0) (real_opp W0))).
      + exact (real_lt_plus_compat_lt_le _ _ _ _ H2 (real_le_refl _)).
      + exact (real_eq_trans
                 (real_plus (real_plus W0 Le0) (real_opp W0))
                 (real_plus W0 (real_plus Le0 (real_opp W0)))
                 Le0
                 (real_eq_sym _ _ (real_plus_assoc W0 Le0 (real_opp W0)))
                 (real_eq_trans
                    (real_plus W0 (real_plus Le0 (real_opp W0)))
                    (real_plus (real_plus W0 (real_opp W0)) Le0)
                    Le0
                    (real_eq_trans
                       (real_plus W0 (real_plus Le0 (real_opp W0)))
                       (real_plus W0 (real_plus (real_opp W0) Le0))
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (RealSetoid.real_eq_plus_compat W0 (real_plus Le0 (real_opp W0)) W0
                          (real_plus (real_opp W0) Le0)
                          (real_eq_refl W0)
                          (real_plus_comm Le0 (real_opp W0)))
                       (real_plus_assoc W0 (real_opp W0) Le0))
                    (real_eq_trans
                       (real_plus (real_plus W0 (real_opp W0)) Le0)
                       (real_plus real_zero Le0)
                       Le0
                       (RealSetoid.real_eq_plus_compat (real_plus W0 (real_opp W0)) Le0
                          real_zero Le0
                          (real_plus_opp W0)
                          (real_eq_refl Le0))
                       (sf_real_plus_zero_l Le0)))). }
  (* Assembly: log(a*kappa^N) == La + -(N#1*(-log kappa)) and La < W + Le give log(a*kappa^N) < Le *)
  assert (Hlt : real_lt (real_log (real_mult a (real_pow kappa N))
                                  (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))
                        (real_log eps Heps)).
  { apply (Hshift _ (real_log a Ha) (real_log eps Heps)
             (real_mult (real_const (Z.of_nat N # 1)) (real_opp (real_log kappa Hk1)))).
    - apply (real_eq_trans _ (real_plus (real_log a Ha)
                   (real_mult (real_const (Z.of_nat N # 1)) (real_log kappa Hk1)))).
      + exact Hlogpow.
      + apply (RealSetoid.real_eq_plus_compat _ _ _ _ (real_eq_refl _) Hnegm).
    - exact Hmid. }
  (* The strict monotonicity of exp plus the e^(log y) == y inversion close the proof *)
  apply (real_eq_lt_lt (real_mult a (real_pow kappa N))
           (cauchy_real_exp (real_log (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1))))
           eps).
  - apply (real_eq_sym _ _ (cw_log_exp_right (real_mult a (real_pow kappa N))
              (real_mult_positive a (real_pow kappa N) Ha (cwe_real_pow_pos kappa N Hk1)))).
  - apply (real_lt_eq_lt _ (cauchy_real_exp (real_log eps Heps))).
    + exact (cauchy_real_exp_mono _ _ Hlt).
    + exact (cw_log_exp_right eps Heps).
Qed.

(* ============ 7. Item 3: the tail-bound shape of theorem 4.10 of paper 4 (pure order algebra) ============ *)

(* Power addition: kappa^(p+j) == kappa^p * kappa^j *)
Lemma real_pow_add_thm : forall (k : Real) (p j : nat),
  real_eq (real_pow k (p + j)%nat) (real_mult (real_pow k p) (real_pow k j)).
Proof.
  intros k p j. induction p as [| p IH].
  - change (real_pow k (0 + j)%nat) with (real_pow k j).
    change (real_pow k 0) with real_one.
    apply (real_eq_sym _ _ (real_mult_one_l (real_pow k j))).
  - replace (Datatypes.S p + j)%nat with (Datatypes.S (p + j))%nat by lia.
    change (real_pow k (Datatypes.S (p + j))) with
           (real_mult k (real_pow k (p + j))).
    apply (real_eq_trans _ (real_mult k (real_mult (real_pow k p) (real_pow k j)))).
    + apply (RealSetoid.real_eq_mult_compat k (real_pow k (p + j)%nat) k
               (real_mult (real_pow k p) (real_pow k j))).
      * apply real_eq_refl.
      * exact IH.
    + apply (real_eq_trans _ (real_mult (real_mult k (real_pow k p)) (real_pow k j))).
      * exact (real_mult_assoc k (real_pow k p) (real_pow k j)).
      * apply real_eq_refl.
Qed.

(* κ ≤ 1 ⟹ κ^j ≤ 1 *)
Lemma real_pow_le_one : forall (k : Real) (Hk1 : real_lt real_zero k)
                          (Hk2 : real_le k real_one) (j : nat),
  real_le (real_pow k j) real_one.
Proof.
  intros k Hk1 Hk2 j. induction j as [| j IH].
  - apply real_le_refl.
  - cbn [real_pow].
    apply (real_le_trans _ (real_mult k real_one)).
    + apply (real_le_trans _ (real_mult (real_pow k j) k)).
      * apply real_eq_le_bridge. exact (real_mult_comm k (real_pow k j)).
      * apply (real_le_trans _ (real_mult real_one k)).
        -- exact (real_le_mult_compat (real_pow k j) real_one k Hk1 IH).
        -- apply real_eq_le_bridge.
           apply (real_eq_trans _ k).
           ++ exact (real_mult_one_l k).
           ++ apply (real_eq_sym _ _ (real_mult_one k)).
      + apply (real_le_trans _ k).
        * apply real_eq_le_bridge. exact (real_mult_one k).
        * exact Hk2.
Qed.

(* Antimonotonicity of powers: 0 < kappa <= 1 and p <= q give kappa^q <= kappa^p *)
Lemma real_pow_anti_mono : forall (k : Real) (Hk1 : real_lt real_zero k)
                              (Hk2 : real_le k real_one) (p q : nat),
  (p <= q)%nat -> real_le (real_pow k q) (real_pow k p).
Proof.
  intros k Hk1 Hk2 p q Hle.
  assert (Hcore : forall j : nat,
            real_le (real_pow k (p + j)%nat) (real_pow k p)).
  { intros j.
    assert (Heq : real_eq (real_pow k (p + j)%nat)
                          (real_mult (real_pow k p) (real_pow k j)))
      by exact (real_pow_add_thm k p j).
    apply (real_le_trans _ (real_mult (real_pow k p) (real_pow k j))).
    - apply real_eq_le_bridge. exact Heq.
    - apply (real_le_trans _ (real_mult (real_pow k j) (real_pow k p))).
      + apply real_eq_le_bridge. exact (real_mult_comm (real_pow k p) (real_pow k j)).
      + apply (real_le_trans _ (real_mult real_one (real_pow k p))).
        * exact (real_le_mult_compat (real_pow k j) real_one (real_pow k p)
                   (cwe_real_pow_pos k p Hk1) (real_pow_le_one k Hk1 Hk2 j)).
        * apply real_eq_le_bridge. exact (real_mult_one_l (real_pow k p)). }
  assert (Hq : q = (p + (q - p))%nat) by lia.
  rewrite Hq. apply Hcore.
Qed.

(* Budget descent: N <= min m n and a*kappa^N < eps give a*kappa^(min m n) < eps
   (the budget proof of the theorem 4.10 tail bound a*kappa^(min m n) of paper 4, pure order algebra) *)
Theorem geo_tail_budget :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps) (m n N : nat),
  (N <= Nat.min m n)%nat ->
  real_lt (real_mult a (real_pow kappa N)) eps ->
  real_lt (real_mult a (real_pow kappa (Nat.min m n))) eps.
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps m n N Hmin Hbudget.
  assert (Hk2le : real_le kappa real_one)
    by exact (real_lt_le_bridge kappa real_one Hk2).
  apply (real_le_lt_trans _ (real_mult a (real_pow kappa N))).
  - apply (real_le_trans _ (real_mult (real_pow kappa (Nat.min m n)) a)).
    + apply real_eq_le_bridge.
      exact (real_mult_comm a (real_pow kappa (Nat.min m n))).
    + apply (real_le_trans _ (real_mult (real_pow kappa N) a)).
      * exact (real_le_mult_compat (real_pow kappa (Nat.min m n))
                  (real_pow kappa N) a Ha
                  (real_pow_anti_mono kappa Hk1 Hk2le N (Nat.min m n) Hmin)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm (real_pow kappa N) a).
  - exact Hbudget.
Qed.

(* The composed form: given the explicit budget N, the min tail bound follows (the Real-layer assembly of theorem 4.10) *)
Theorem budget_min_tail :
  forall (kappa a eps : Real)
         (Hk1 : real_lt real_zero kappa) (Hk2 : real_lt kappa real_one)
         (Ha : real_lt real_zero a) (Heps : real_lt real_zero eps),
  sigT (fun N : nat => forall (p q : nat),
    (N <= Nat.min p q)%nat ->
    real_lt (real_mult a (real_pow kappa (Nat.min p q))) eps).
Proof.
  intros kappa a eps Hk1 Hk2 Ha Heps.
  destruct (r_arch_pow_real kappa Hk1 Hk2 a Ha eps Heps) as [N HN].
  exists N.
  intros p q Hpq.
  exact (geo_tail_budget kappa a eps Hk1 Hk2 Ha Heps p q N Hpq HN).
Qed.

(* ============ 8. The extraction check (executable OCaml, the G3 check) ============ *)
Set Warnings "-extraction-opaque-accessed".
Extraction "upbudgetreal.ml" r_arch_pow_real budget_cond_sufficient geo_tail_budget budget_min_tail.

End BudgetReal.

(* ---------- UpArchAttn ---------- *)
From Stdlib Require Import QArith.QArith.
Import BudgetReal.

(*  -- hot-spot entry A3: the Real-layer copy of r_arch_pow_attn *)
(* Scan source (entry A3 of the analysis-219 hot-spot scan): *)
(*   the interface premise of the root attention-convergence region *)
(*     Variable r_arch_pow_attn :                                *)
(*       forall (a : R), lt zero a -> forall eps : R, lt zero eps -> *)
(*         sigT (fun N : nat =>                                  *)
(*           lt (mult a (r_pow (minus one delta) N)) eps),        *)
(*   is the N supply port of the geometric-decay assumption attention_iterate_converges (L29330). *)
(*   It is isomorphic to the upgraded r_arch_pow of the convergence region (ConvergenceCauchy L14081), *)
(*   yet was never connected to the accepted Real-layer budget machine UpBudgetReal.r_arch_pow_real *)
(*   (sigT N, a*kappa^N < eps for 0 < kappa < 1, 0 < a, 0 < eps). This file removes the disconnection: *)
(* Item 1 (main item) r_arch_pow_attn_real: the instantiation of the interface premise at the concrete Real layer. *)
(*   The shape-alignment map (the verification verdict): *)
(*     R (abstract, the instance carrier of RealInterfaceEnhanced) *)
(*         maps to Real (the Cauchy reals sigT (u : Qseq) (cauchy u)) *)
(*     lt zero / lt maps to real_lt real_zero / real_lt (the Type version) *)
(*     mult ⟿ real_mult                                          *)
(*     minus one delta ⟿ real_plus real_one (real_opp delta)      *)
(*       (the Real layer has no subtraction notation; x-y := x+(-y), the convention of root L41051) *)
(*     r_pow (the root L14071 Fixpoint: O maps to one, S m maps to mult x (pow x m), *)
(*       the left-multiplication form) maps to real_pow (the UpBudgetReal L46 Fixpoint: *)
(*       O maps to real_one, S m maps to real_mult x (pow x m) -- the same left-multiplication form; *)
(*       definitional isomorphism confirmed: the bridge is a definition-level instantiation (the root r_pow lives in the abstract R world, *)
(*       a cross-world real_eq bridge cannot be typed; UpBudgetReal already fixed the Notation *)
(*       r_pow := real_pow, so the interface name and the function coincide at the Real layer). *)
(*     The Section Variables delta/delta_pos/delta_lt_one (they vanish once the section closes) *)
(*         become the explicit premises of the statement. *)
(* Item 2 (assembly rehearsal) attention_iterate_converges_real: *)
(*   It depends on item 1 plus the Real copy of the conclusion of the root attention_tv_iter_contraction (L29287): *)
(*   the copy chain tv_n <= (1-delta)^n*tv_0 (the Real copy of the root r_pow_dec_iter_attn *)
(*   is exactly UpBudgetReal.real_pow_anti_mono, reused directly), *)
(*   giving the sigT budget-N witness theorem. Coverage note: the semantic objects of the root theorem *)
(*   attention_step/tv_dist/boltzmann_dist_attn live in the abstract Section *)
(*   world; instantiating them requires proving, wholesale at the Real layer, the matching interface premises *)
(*   detailed_balance/minorization/sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat *)
(*   (day-scale work, outside this small file); per the original task statement, the Real sequence *)
(*   tv_seq := n maps to TV(iterate n mu0, p_b) carries the minimal skeleton, with the per-step geometric *)
(*   contraction listed explicitly as the copy premise Hstep. Item 1 is unaffected. *)
(* Discipline: purely constructive; Set-level statements (real_lt/real_le/real_eq/sigT); *)
(*       closed by Qed throughout; depending only on machines proved in the root and in UpBudgetReal. *)


Local Open Scope Q_scope.

(* ============ 1. Real-layer order lemmas for 1-delta (the premises that make kappa := 1-delta well defined) ============ *)

(* The Real copy of the root L14270 one_minus_kappa_pos: delta < 1 gives 0 < 1-delta *)
Lemma one_minus_delta_pos_real : forall delta : Real,
  real_lt delta real_one ->
  real_lt real_zero (real_plus real_one (real_opp delta)).
Proof.
  intros delta Hd.
  exact (real_lt_opp_plus delta real_one Hd).
Qed.

(* The Real copy of the symmetric branch of the root attention-region premise: 0 < delta gives 1-delta < 1
   (pointwise zero difference plus real_lt_eq_lt: 1-(1-delta) == delta by the pointwise ring) *)
Lemma one_minus_delta_lt_one_real : forall delta : Real,
  real_lt real_zero delta ->
  real_lt (real_plus real_one (real_opp delta)) real_one.
Proof.
  intros delta Hd.
  apply (real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one).
  apply (real_lt_eq_lt real_zero delta).
  - exact Hd.
  - apply real_eq_sym.
    apply real_eq_of_zero_diff.
    intro n.
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one
               (real_opp (real_plus real_one (real_opp delta))) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj (real_plus real_one (real_opp delta)) n)).
    rewrite (qeqT_imp_qeq _ _ (real_plus_proj real_one (real_opp delta) n)).
    rewrite (qeqT_imp_qeq _ _ (real_opp_proj delta n)).
    cbn [projT1].
    ring.
Qed.

(* ============ 2. Item 1, main piece: the Real-layer instantiation of the interface premise ============ *)

Theorem r_arch_pow_attn_real :
  forall delta : Real, real_lt real_zero delta -> real_lt delta real_one ->
  forall a : Real, real_lt real_zero a ->
  forall eps : Real, real_lt real_zero eps ->
  sigT (fun N : nat =>
    real_lt (real_mult a
              (real_pow (real_plus real_one (real_opp delta)) N)) eps).
Proof.
  intros delta Hd1 Hd2 a Ha eps Heps.
  exact (r_arch_pow_real (real_plus real_one (real_opp delta))           (one_minus_delta_pos_real delta Hd2)           (one_minus_delta_lt_one_real delta Hd1)           a Ha eps Heps).
Qed.

(* ============ 3. Item 2, assembly rehearsal: the TV geometric decay chain (Real copy) ============ *)

(* The Real copy chain of the conclusion of the root attention_tv_iter_contraction:
   each step tv_{n+1} <= (1-delta)*tv_n gives tv_n <= (1-delta)^n*tv_0.
   (the Real copy of the power antimonotonicity of the root r_pow_dec_iter_attn is exactly
     UpBudgetReal.real_pow_anti_mono; the item 2 main theorem reuses it directly, without re-proving.) *)
Lemma tv_iter_decay_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall n : nat,
    real_le (tv_seq n)
            (real_mult (real_pow (real_plus real_one (real_opp delta)) n)
                       (tv_seq Datatypes.O)).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep n.
  assert (Hk1 : real_lt real_zero (real_plus real_one (real_opp delta)))
    by exact (one_minus_delta_pos_real delta Hd2).
  set (kappa := real_plus real_one (real_opp delta)) in *.
  induction n as [| n IH].
  - (* kappa^0 is one: 1*tv_0 == tv_0 *)
    apply real_eq_le_bridge.
    apply real_eq_sym.
    exact (real_mult_one_l (tv_seq Datatypes.O)).
  - (* tv_{n+1} <= kappa*tv_n <= kappa*(kappa^n*tv_0) == kappa^(n+1)*tv_0 *)
    apply (real_le_trans _ (real_mult kappa (tv_seq n))).
    + exact (Hstep n).
    + apply (real_le_trans _ (real_mult (tv_seq n) kappa)).
      * apply real_eq_le_bridge.
        exact (real_mult_comm kappa (tv_seq n)).
      * apply (real_le_trans _
                 (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                            kappa)).
        -- exact (real_le_mult_compat (tv_seq n)
                    (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                    kappa Hk1 IH).
        -- apply real_eq_le_bridge.
           exact (real_eq_trans
                    (real_mult (real_mult (real_pow kappa n) (tv_seq Datatypes.O))
                               kappa)
                    (real_mult kappa
                               (real_mult (real_pow kappa n) (tv_seq Datatypes.O)))
                    (real_mult (real_mult kappa (real_pow kappa n))
                               (tv_seq Datatypes.O))
                    (real_mult_comm (real_mult (real_pow kappa n)
                                        (tv_seq Datatypes.O))
                                    kappa)
                    (real_mult_assoc kappa (real_pow kappa n)
                                     (tv_seq Datatypes.O))).
Qed.

(* ============ 4. Item 2, main theorem: the sigT explicit budget witness of iterative convergence ============ *)

(* The Real-layer copy assembly of the root attention_iterate_converges:
   the budget N is constructed by item 1 (r_arch_pow_attn_real); the tail bound n >= N comes from
   the TV decay chain (the item 2 prelude of this file) plus the power antimonotonicity (real_pow_anti_mono)
   together with the a*kappa^N < eps proof of item 1.
   Coverage note: tv_seq is the Real carrier of the root semantic object n maps to TV(iterate attention_step n mu0,
   boltzmann_dist_attn); the per-step contraction Hstep matches the conclusion shape of the root
   attention_tv_contraction. The full Real-layer instantiation of the root abstract Section
   requires wholesale proofs of detailed_balance/minorization/
   sum_swap_cc/abs_ge_zero_id_cc/lt_plus_compat as matching interface premises;
   that is day-scale work, outside this small file (item 1 is unaffected). *)
Theorem attention_iterate_converges_real :
  forall (delta : Real)
         (Hd1 : real_lt real_zero delta) (Hd2 : real_lt delta real_one)
         (tv_seq : nat -> Real),
  (forall n : nat,
    real_le (tv_seq (Datatypes.S n))
            (real_mult (real_plus real_one (real_opp delta)) (tv_seq n))) ->
  forall eps : Real, real_lt real_zero eps ->
  real_lt real_zero (tv_seq Datatypes.O) ->
  sigT (fun N : nat => forall n : nat, (N <= n)%nat ->
    real_lt (tv_seq n) eps).
Proof.
  intros delta Hd1 Hd2 tv_seq Hstep eps Heps Htv0.
  destruct (r_arch_pow_attn_real delta Hd1 Hd2
             (tv_seq Datatypes.O) Htv0 eps Heps) as [N HN].
  exists N.
  intros n Hn.
  set (kappa := real_plus real_one (real_opp delta)) in *.
  apply (real_le_lt_trans _
           (real_mult (real_pow kappa n) (tv_seq Datatypes.O))).
  - exact (tv_iter_decay_real delta Hd1 Hd2 tv_seq Hstep n).
  - apply (real_le_lt_trans _
             (real_mult (real_pow kappa N) (tv_seq Datatypes.O))).
    + assert (Hk1 : real_lt real_zero kappa)
        by exact (one_minus_delta_pos_real delta Hd2).
      assert (Hk2le : real_le kappa real_one)
        by exact (real_lt_le_bridge kappa real_one
                    (one_minus_delta_lt_one_real delta Hd1)).
      assert (Hanti : real_le (real_pow kappa n) (real_pow kappa N))
        by exact (real_pow_anti_mono kappa Hk1 Hk2le N n Hn).
      exact (real_le_mult_compat (real_pow kappa n) (real_pow kappa N)
               (tv_seq Datatypes.O) Htv0 Hanti).
    + exact (real_eq_lt_lt (real_mult (real_pow kappa N) (tv_seq Datatypes.O))
               (real_mult (tv_seq Datatypes.O) (real_pow kappa N)) eps
               (real_mult_comm (real_pow kappa N) (tv_seq Datatypes.O)) HN).
Qed.

(* ============ 5. The extraction check (G3: zero Obj.magic) ============ *)

Extraction "uparchattn.ml" r_arch_pow_attn_real attention_iterate_converges_real.


Print Assumptions r_arch_pow_attn_real.
Print Assumptions one_minus_delta_pos_real.
Print Assumptions SigMigrate.req_mult_one_l.
Print Assumptions SigMigrate.req_plus_zero_r.
Print Assumptions hlogz_discharge_full.
