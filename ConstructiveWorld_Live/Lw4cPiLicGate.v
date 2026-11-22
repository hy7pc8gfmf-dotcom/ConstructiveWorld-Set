(* ConstructiveWorld-Set -- pi-side lic escape window supply: guard-to-window transcription, boolean decider, budgeted search. *)

(** * Lw4cPiLicGate: transcription of the pi-side escape guard into lic escape window witnesses.

    Mission.  Assemble the window transcription of the pi-side supply face
      [lw4c_pi_lic_face = lic_escape_window lw0m_xL lw4c_pi_win]: the escape guard
      (window distance doubled by precision [2*c0], the leibsep outer-branch premise
      shape) becomes a lic escape window witness; the boolean decider [lw4p_licdec] bridges
      both ways to the guard, and budgeted generic search returns escape orders ([lw4p_escape_by_find]).

    Dependencies.  Stdlib [QArith.QArith QArith.Qabs ZArith.ZArith], [Arith.Arith], [Bool.Bool], [Lia], [Extraction].  Requires [S01_BaseRing] (And/NatLe/id_refl),
      [S02_CauchyComplete] (QltT/real_lt), [LW0LeibWindow] (leiblw_Id, leiblw_Qleb,
      leiblw_id_eq, leiblw_id_inv_in), [PiEnvelope] (pie_mag), [LW0MLicBridge] (lw0m_e, lw0m_xL),
      [LW4EPiContrast] (lw4c_pi_win, lw4c_pi_lic_face, lw4c_pi_escape), [NsepFindGeneric]
      (nsep_find, nsep_find_hit, nsep_find_ub), [LW5SepComplexity] (lw5n_Qleb_false_lt,
      lw5n_qltT'_qlt, lw5n_qleb_inv_eq), [UpReqIrrationalCriterion] (lic_escape_window).

    References.  LW4EPiContrast.v:67/:72/:99 (the three use targets); UpReqIrrationalCriterion.v:242
      (lic_escape_window shape); LW0MLicBridge.v:16/:20 (window distance, sequence names);
      LW0LeibSeparation.v:53/:220/:298 (escape gate, outer branch, alpha guard shape; premise
      shapes aligned verbatim); NsepFindGeneric.v:45/:67; LW5SepComplexity.v:301 (decider source).

    Constructivity.  The statement face is entirely Set-layer (sigT, And, QltT, leiblw_Id); the
      [(1 <= N)%nat] arrow premise follows the certified precedent of leiblw_natwin_unbounded
      and lw4c_e_win_lt_pi_win; zero admissions, zero classical logic, purely computational
      decider.  Honest boundary: the unconditional face (positive distance from pi to every rational)
      is the LW0LeibSeparation inner branch, not claimed here; [lw4p_pi_gate_supply] lifts to
      [lw4c_pi_lic_face] in one step ([lw4p_pi_lic_face_of_gate]), no independence claims.

    Build.  [coqc -native-compiler no -q -Q . "" -Q "D:/ComplexAnalysis/ConstructiveWorld-Main/ConstructiveWorld_vo" "" Lw4cPiLicGate.v] compiles cleanly (exit 0); the artifact starts with [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Arith.Arith Bool.Bool Lia.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import LW0LeibWindow.
Require Import PiEnvelope.
Require Import LW0MLicBridge.
Require Import LW4EPiContrast.
Require Import NsepFindGeneric.
Require Import LW5SepComplexity.
Require Import UpReqIrrationalCriterion.

(* ============================================================ *)
(* S1 window width compatibility: the pi-side window is 5 * pie_mag n = *)
(*    5/(2n+1) (the same one-step ring computation as the LW4EPiContrast A2 *)
(*    branch); the base identity tying the leibsep escape gate and the lic *)
(*    window to one common width. *)
(* ============================================================ *)

Lemma lw4p_win_eq : forall n : nat,
  lw4c_pi_win n == (5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q.
Proof.
  intro n. unfold lw4c_pi_win, lw0m_e, pie_mag, Qdiv. ring.
Qed.

(* ============================================================ *)
(* S2 escape-guard micro piece: the strengthened window-distance premise gives *)
(*    the pointwise escape-window inequality (a pure Q-arithmetic chain: *)
(*    win N <= win N + 2*c0 < |xL N - q| = |q - xL N|). *)
(* ============================================================ *)

Lemma lw4p_win_lt_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  QltT (lw4c_pi_win N) (Qabs ((q - lw0m_xL N)%Q)).
Proof.
  intros q N c0 Hc0 Hg.
  pose proof (QltT_to_Qlt (lw4c_pi_win N + 2 * c0)%Q
               (Qabs ((lw0m_xL N - q)%Q)) Hg) as Hg'.
  pose proof (QltT_to_Qlt 0%Q c0 Hc0) as Hlt0.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans (lw4c_pi_win N) (lw4c_pi_win N + 2 * c0)%Q
           (Qabs ((q - lw0m_xL N)%Q))).
  - apply (Qle_trans (lw4c_pi_win N) (lw4c_pi_win N + 0)%Q
             (lw4c_pi_win N + 2 * c0)%Q).
    + rewrite Qplus_0_r. apply Qle_refl.
    + apply (proj2 (Qplus_le_r 0%Q (2 * c0)%Q (lw4c_pi_win N))).
      apply (Qle_trans 0%Q c0%Q (2 * c0)%Q).
      * apply Qlt_le_weak. exact Hlt0.
      * assert (E : (2 * c0)%Q == (c0 + c0)%Q) by ring. rewrite E.
        apply (Qle_trans c0%Q (c0 + 0)%Q (c0 + c0)%Q).
        -- rewrite Qplus_0_r. apply Qle_refl.
        -- apply (Qplus_le_compat c0%Q c0%Q 0%Q c0%Q).
           ++ apply Qle_refl.
           ++ apply Qlt_le_weak. exact Hlt0.
  - rewrite (Qabs_Qminus q (lw0m_xL N)). exact Hg'.
Qed.

(* ============================================================ *)
(* S3 escape guard implies the pi-side escape window witness (direct use of *)
(*    the target lw4c_pi_escape; the in-window block transcribed in And form; *)
(*    the gate-shaped total supply type plus its one-step lifting theorem). *)
(* ============================================================ *)

Theorem lw4p_escape_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  (1 <= N)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  lw4c_pi_escape q.
Proof.
  intros q N c0 HN Hc0 Hg.
  exists N. exists HN.
  exact (lw4p_win_lt_of_guard q N c0 Hc0 Hg).
Qed.

Theorem lw4p_lic_block_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  (1 <= N)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  sigT (fun n : nat =>
    And ((1 <= n)%nat)
        (QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)))).
Proof.
  intros q N c0 HN Hc0 Hg. exists N. split.
  - exact HN.
  - exact (lw4p_win_lt_of_guard q N c0 Hc0 Hg).
Qed.

(* Gate-shaped total supply type: gate data (N, c0) for each q. The unconditional *)
(*    supply of this type equals positive-distance separation of pi from every *)
(*    rational (the inner-branch continuation face); this module carries the gap *)
(*    explicitly at the type position (honest boundary). *)
Definition lw4p_pi_gate_supply : Set :=
  forall q : Q,
    sigT (fun N : nat =>
      sigT (fun c0 : Q =>
        And ((1 <= N)%nat)
            (And (QltT 0 c0)
                 (QltT (lw4c_pi_win N + 2 * c0)%Q
                       (Qabs ((lw0m_xL N - q)%Q)))))).

Theorem lw4p_pi_lic_face_of_gate : lw4p_pi_gate_supply -> lw4c_pi_lic_face.
Proof.
  intro Hs. intro q.
  destruct (Hs q) as [N [c0 [HN [Hc0 Hg]]]].
  exact (lw4p_lic_block_of_guard q N c0 HN Hc0 Hg).
Qed.

(* ============================================================ *)
(* S4 the boolean separation decider for the lic window shape (the *)
(*    lw5n_sep_dec isomorphic form) and its two bridges. *)
(* ============================================================ *)

Definition lw4p_licdec (q : Q) (n : nat) : bool :=
  negb (leiblw_Qleb (Qabs ((q - lw0m_xL n)%Q)) (lw4c_pi_win n)).

Lemma lw4p_licdec_true : forall (q : Q) (n : nat),
  lw4p_licdec q n = true ->
  QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)).
Proof.
  intros q n H. unfold lw4p_licdec in H. apply negb_true_iff in H.
  apply Qlt_to_QltT. exact (lw5n_qltT'_qlt _ _ (lw5n_Qleb_false_lt _ _ H)).
Qed.

Lemma lw4p_licdec_of_escape : forall (q : Q) (n : nat),
  QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)) ->
  lw4p_licdec q n = true.
Proof.
  intros q n H. pose proof (QltT_to_Qlt _ _ H) as Hlt.
  unfold lw4p_licdec.
  destruct (leiblw_Qleb (Qabs ((q - lw0m_xL n)%Q)) (lw4c_pi_win n)) eqn:E;
    simpl.
  - exfalso. pose proof (lw5n_qleb_inv_eq _ _ E) as Hle.
    exact (Qlt_irrefl (lw4c_pi_win n) (Qlt_le_trans _ _ _ Hlt Hle)).
  - reflexivity.
Qed.

Lemma lw4p_licdec_of_guard : forall (q : Q) (N : nat) (c0 : Q),
  (1 <= N)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  lw4p_licdec q N = true.
Proof.
  intros q N c0 HN Hc0 Hg. apply lw4p_licdec_of_escape.
  exact (lw4p_win_lt_of_guard q N c0 Hc0 Hg).
Qed.

(* ============================================================ *)
(* S5 generic decider application face: budgeted search supplies the escape *)
(*    order mechanically. *)
(* ============================================================ *)

Definition lw4p_escape_by_find (q : Q) (b : nat) : nat :=
  nsep_find lw4p_licdec q 1 b.

Lemma lw4p_find_ge1 : forall (q : Q) (b n : nat), (1 <= n)%nat ->
  (1 <= nsep_find lw4p_licdec q n b)%nat.
Proof.
  intros q b. induction b as [|b IH]; intros n Hn; simpl.
  - exact Hn.
  - destruct (lw4p_licdec q n).
    + exact Hn.
    + apply IH. lia.
Qed.

Lemma lw4p_find_ub : forall (q : Q) (b : nat),
  (lw4p_escape_by_find q b <= 1 + b)%nat.
Proof.
  intros q b. unfold lw4p_escape_by_find.
  pose proof (nsep_find_ub lw4p_licdec q b 1) as H. lia.
Qed.

Lemma lw4p_find_escape : forall (q : Q) (b n0 : nat),
  (1 <= n0)%nat -> (n0 <= 1 + b)%nat ->
  QltT (lw4c_pi_win n0) (Qabs ((q - lw0m_xL n0)%Q)) ->
  QltT (lw4c_pi_win (lw4p_escape_by_find q b))
       (Qabs ((q - lw0m_xL (lw4p_escape_by_find q b))%Q)).
Proof.
  intros q b n0 H1 H2 Hesc. unfold lw4p_escape_by_find.
  assert (Hdec : leiblw_Id (lw4p_licdec q n0) true).
  { rewrite (lw4p_licdec_of_escape q n0 Hesc). apply leiblw_id_intro. }
  destruct (nsep_find_hit lw4p_licdec q b 1 n0 H1 H2 Hdec) as [Hh _].
  leiblw_id_inv_in Hh.
  apply lw4p_licdec_true. exact Hh.
Qed.

(* Escape guard implies the budgeted search hits an escape order (the full *)
(*    chain from gate data to a computational witness closes here). *)
Theorem lw4p_find_escape_of_guard : forall (q : Q) (b N : nat) (c0 : Q),
  (1 <= N)%nat -> (N <= 1 + b)%nat -> QltT 0 c0 ->
  QltT (lw4c_pi_win N + 2 * c0)%Q (Qabs ((lw0m_xL N - q)%Q)) ->
  QltT (lw4c_pi_win (lw4p_escape_by_find q b))
       (Qabs ((q - lw0m_xL (lw4p_escape_by_find q b))%Q)).
Proof.
  intros q b N c0 H1 H2 Hc0 Hg.
  exact (lw4p_find_escape q b N H1 H2
          (lw4p_win_lt_of_guard q N c0 Hc0 Hg)).
Qed.

(* ============================================================ *)
(* S6 numerical spot checks (closed terms on the computational face; at *)
(*    q = 0 the window is escaped already at order 1: 8/3 > 5/3). *)
(* ============================================================ *)

Lemma lw4p_licdec_tbl_zero : leiblw_Id (lw4p_licdec 0%Q 1) true.
Proof. apply leiblw_id_eq. reflexivity. Qed.

Eval vm_compute in
  (lw4p_escape_by_find (22 # 7)%Q 200,
   lw4p_escape_by_find (3 # 1)%Q 200,
   lw4p_escape_by_find 0%Q 3).

(* ============================================================ *)
(* S7 extraction plus the assumptions audit (red-line item 4). *)
(* ============================================================ *)

Separate Extraction lw4p_licdec lw4p_escape_by_find lw4p_win_eq
  lw4p_escape_of_guard lw4p_find_escape lw4p_pi_lic_face_of_gate.

Print Assumptions lw4p_escape_of_guard.
Print Assumptions lw4p_find_escape.
Print Assumptions lw4p_pi_lic_face_of_gate.
Print Assumptions lw4p_licdec_true.
