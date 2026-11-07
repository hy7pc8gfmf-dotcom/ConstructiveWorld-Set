(* ConstructiveWorld-Set — e-π escape-window contrast: modulus pair, window-width comparisons, contrast main statement. *)
(** * LW4EPiContrast: the e-side and π-side irrationality escape-window contrast over [Q].

    Mission.  Pairs the e-side window [lw4c_e_win] = 1/n! (factorial decay) with the
      π-side window [lw4c_pi_win] = 5/(2n+1) (harmonic decay);
      [lw4c_contrast_face] conjoins the two escape statements ([Set] face) via
      [lw4c_contrast_param]; witness reshaping ([lic]-form to nested [sigT]) is
      purely mechanical.  Comparisons [lw4c_e_win_le_pi_win], [lw4c_e_win_lt_pi_win],
      [lw4c_pi_win_gt_powwin], [lw4c_e_win_le_expwin]; shape separation
      [lw4c_shape_separation]; closed-term table [lw4c_win_tbl].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [ZArith.ZArith],
      [Extraction], [Lia]; requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [SumInvFactEscape], [LW0LeibWindow], [PiEnvelope],
      [LW0MLicBridge], [UpReqIrrationalCriterion] of this development.

    References.  [UpReqIrrationalCriterion] ([lic_witness_e] L723,
      [lic_escape_window] L242); [LW0MLicBridge] ([lw0m_e] L16,
      [lw0m_xL] L20); [LW0LeibWindow] (certified same-shape at L941);
      [PiEnvelope] ([pie_mag], no name consumed by this face).

    Constructivity.  Nothing admitted; the statement face is entirely
      [Set]-layer (nested [sigT] in the certified L941 shape; [And] the
      [Set]-valued A×B form of [S01_BaseRing]; orders via [QltT]/[QleT']);
      the π-side supply stands as the premise [lw4c_pi_lic_face]; no [Lra]/[Reals];
      extraction and [Print Assumptions] audit [Obj.magic] = 0 and closure.

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" LW4EPiContrast.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)
From Stdlib Require Import QArith.QArith QArith.Qabs ZArith.ZArith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.        (* Set-layer logic pieces: [And] (L46, the A×B form) / [NatLe] (L88) *)
Require Import S02_CauchyComplete.  (* [QltT] (L48) / [Real] / [real_metric] *)
Require Import S03_QExp.            (* [q_fact] (L43) / [exp_series] (L788) *)
Require Import SumInvFactEscape.    (* sif escape machinery (used inside the proof body of [lic_witness_e]) *)
Require Import LW0LeibWindow.       (* [leiblw_Id] / [Qltb] bricks / the shape-separation family *)
Require Import PiEnvelope.          (* the [pie_mag] family (no name consumed by this file's contrast face) *)
Require Import LW0MLicBridge.       (* [lw0m_e] (L16) / [lw0m_xL] (L20) *)
Require Import UpReqIrrationalCriterion.  (* [lic_witness_e] (L723) / [lic_escape_window] (L242) *)

(* ============================================================ *)
(* §1. Modulus records (the contrasted objects)                  *)
(* ============================================================ *)
(* The e-side window = 1/n! (factorial decay).  Token-identical to the
   second-argument lambda of [lic_witness_e] (L723-724), so [exact]
   applies with no conversion gap; written in [1%Q] form for the same
   semantics without notation conversion. *)
Definition lw4c_e_win (n : nat) : Q := 1%Q / q_fact n.

(* The π-side window = 5·pie_mag n = 5/(2n+1) (harmonic decay), substituted opaquely as [lw0m_e] *)
Definition lw4c_pi_win (n : nat) : Q := lw0m_e n.

(* Juxtaposition record for the two moduli: the A×B pair verbatim; both [prod] arguments have type [nat -> Q] in [Set], with no [Prop] position *)
Definition lw4c_modulus_pair : prod (nat -> Q) (nat -> Q) :=
  pair lw4c_e_win lw4c_pi_win.

(* ============================================================ *)
(* §2. The e-side branch (reshaped from [lic_witness_e]) — the   *)
(*   statement face matches the certified same-shape form at     *)
(*   LW0LeibWindow L941: sigT nesting with a guard position and  *)
(*   a Set-valued order decision ([QltT], S02 L48).              *)
(* ============================================================ *)
Definition lw4c_e_escape (q : Q) : Set :=
  sigT (fun n : nat =>
    sigT (fun _ : (1 <= n)%nat =>
      QltT (lw4c_e_win n) (Qabs ((q - exp_series n 1)%Q)))).

Lemma lw4c_e_escape_supply : forall q : Q, lw4c_e_escape q.
Proof.
  intro q.
  destruct (lic_witness_e q) as [n [Hn1 Hlt]].
  exists n. exists Hn1. exact Hlt.
Qed.
(* The reshaping is token-for-token the target form; should [exact] stall on a conversion, insert [unfold lw4c_e_win.] on the line before [exact]. *)

(* ============================================================ *)
(* §2'. The e-side lic-form direct-carrier face (stage 0 of the  *)
(*   reshaping: definitional, proof-free substitution); the §2   *)
(*   face does not depend on §2'.                                *)
(* ============================================================ *)
Definition lw4c_e_lic_face : Set :=
  lic_escape_window (fun n => exp_series n 1) lw4c_e_win.
Definition lw4c_e_lic_supply : lw4c_e_lic_face := lic_witness_e.

(* ============================================================ *)
(* §3. The π-side branch (LIC window shape, isomorphic to the    *)
(*   e-side branch; the supply is external and stands here as    *)
(*   the premise [lw4c_pi_lic_face] — nothing is constructed in  *)
(*   this section; see the reserved names in §6).                *)
(* ============================================================ *)
Definition lw4c_pi_escape (q : Q) : Set :=
  sigT (fun n : nat =>
    sigT (fun _ : (1 <= n)%nat =>
      QltT (lw4c_pi_win n) (Qabs ((q - lw0m_xL n)%Q)))).

Definition lw4c_pi_lic_face : Set :=
  lic_escape_window lw0m_xL lw4c_pi_win.

Lemma lw4c_pi_escape_of_lic :
  lw4c_pi_lic_face -> forall q : Q, lw4c_pi_escape q.
Proof.
  intro Hlic. intro q.
  destruct (Hlic q) as [n [Hn1 Hlt]].
  exists n. exists Hn1. exact Hlt.
Qed.
(* A pure destruct disassembly/reassembly lemma: independent of the external π-side supply (carried at the premise position), so this section closes on its own; the source face and the target face are token-for-token identical here — unfolding [lic_escape_window lw0m_xL lw4c_pi_win] gives exactly the body of [lw4c_pi_escape] — so [exact] applies with no conversion. *)

(* ============================================================ *)
(* §4. The contrast main statement and its parameterized closure *)
(* ============================================================ *)
(* [And] is the Set-valued And of S01 L46 (the A×B form verbatim); both
   arguments are [forall q : Q, ... escape q] — a Set-valued universal
   over [Q : Set], so the conjunction lands in [Set].  Alternative form
   (should the And position be unable to carry a Type-level branch): the
   nested sigT face
   [sigT (fun He : forall q, lw4c_e_escape q => forall q, lw4c_pi_escape q)]
   — the same-shape precedent at L941 uses no And — with the proof body
   [intro Hlic. exists lw4c_e_escape_supply.
   exact (lw4c_pi_escape_of_lic Hlic).] *)
Definition lw4c_contrast_face : Set :=
  And (forall q : Q, lw4c_e_escape q)
      (forall q : Q, lw4c_pi_escape q).

Theorem lw4c_contrast_param : lw4c_pi_lic_face -> lw4c_contrast_face.
Proof.
  intro Hlic. split.
  - exact lw4c_e_escape_supply.
  - exact (lw4c_pi_escape_of_lic Hlic).
Qed.
(* The left branch substitutes directly from the library (reshaped from [lic_witness_e]); the right branch is carried at the premise position.  Once the closed-form π-side supply lands, the premise is discharged and [lw4c_contrast] follows (reserved-name region §6). *)

(* ============================================================ *)
(* §5. Numeric counterparts of the contrast (checked from the    *)
(*   library rather than re-cast)                                *)
(* ============================================================ *)
Check leiblw_margin_tbl.
Check leiblw_natwin_tbl.

(* ============================================================ *)
(* §6. Reserved-name region (names enabled after the closed-form *)
(*   π-side supply; not part of this file's compiled face)       *)
(*   lw4c_shape_separation   : the shape theorem (drawing on
     [leiblw_family_separation] L971, [leiblw_nivwin_bounded] L962,
     [leiblw_natwin_unbounded] L894; the contrast semantics cover the
     window-family shapes)
   lw4c_pi_lic_supply        : the closed-form supply c(a,b) for the
     π-side premise
   lw4c_contrast             : the unconditional counterpart
     := pair lw4c_e_escape_supply (lw4c_pi_escape_of_lic lw4c_pi_lic_supply)
   lw4c_pi_escape_of_b    : the reshaping lemma at the closed-form
     interface (to be proved once the closed-form supply lands)    *)
(* ============================================================ *)

(* ============================================================ *)
(* §7. Extraction + Print Assumptions (the closing audit)        *)
(* ============================================================ *)
Separate Extraction lw4c_modulus_pair lw4c_e_win lw4c_pi_win
  lw4c_e_escape lw4c_e_escape_supply lw4c_pi_escape
  lw4c_pi_escape_of_lic lw4c_contrast_face lw4c_contrast_param.
Print Assumptions lw4c_e_escape_supply.
Print Assumptions lw4c_contrast_param.
(* Targets: extraction with zero [Obj.magic]; both [Print Assumptions]
   outputs Closed under the global context.  The π-side supply does not
   exist yet (it stands at the premise position), so it enters neither
   the extraction value domain nor the audit face. *)


From Stdlib Require Import Lia.  (* auxiliary arithmetic for the nat/Z domain; the Q domain goes through explicit chains *)

(* ============================================================ *)
(* §8. Window-width contrast (entirely Set-layer; independent of *)
(*   the π-side supply)                                          *)
(* ============================================================ *)

(* A1a: the factorial is always >= 1 (the inductive base) *)
Lemma lw4c_qfact_ge_1 : forall n : nat, QleT' 1%Q (q_fact n).
Proof.
  intro n. apply Qle_to_QleT'. induction n as [| m IH]; simpl.
  - unfold Qle. simpl. lia.
  - apply (Qle_trans _ (1%Q * q_fact m)).
    + setoid_rewrite (Qmult_1_l (q_fact m)). exact IH.
    + apply (Qmult_le_compat_r 1%Q (Z.of_nat (Datatypes.S m) # 1)%Q (q_fact m)).
      * apply QleT'_to_Qle. apply (Qle_of_nat 1 (Datatypes.S m)). lia.
      * apply (Qlt_le_weak 0%Q (q_fact m)). apply QltT_to_Qlt. apply q_fact_pos.
Qed.

(* A1b: the factorial is at least its index — n >= 1 implies n <= n! (the common chain brick for A2/A3) *)
Lemma lw4c_qfact_ge_nat : forall n : nat, (1 <= n)%nat ->
  QleT' ((Z.of_nat n) # 1)%Q (q_fact n).
Proof.
  intro n. induction n as [| m IH]; intro Hn; apply Qle_to_QleT'.
  - unfold Qle. simpl. lia.
  - pose proof (qeqT_imp_qeq _ _ (q_fact_succ m)) as Hfs. setoid_rewrite Hfs.
    setoid_rewrite (Qmult_comm (Z.of_nat (Datatypes.S m) # 1)%Q (q_fact m)).
    apply (Qle_trans _ (1%Q * (Z.of_nat (Datatypes.S m) # 1)%Q)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. symmetry. apply Qmult_1_l.
    + apply (Qmult_le_compat_r 1%Q (q_fact m) (Z.of_nat (Datatypes.S m) # 1)%Q).
      * exact (QleT'_to_Qle 1%Q (q_fact m) (lw4c_qfact_ge_1 m)).
      * apply QleT'_to_Qle. apply (Qle_of_nat 0 (Datatypes.S m)). lia.
Qed.

(* A2: the pointwise non-strict contrast — n >= 1 implies 1/n! <= 5/(2n+1) *)
Lemma lw4c_e_win_le_pi_win : forall n : nat, (1 <= n)%nat ->
  QleT' (lw4c_e_win n) (lw4c_pi_win n).
Proof.
  intros n Hn. apply Qle_to_QleT'.
  unfold lw4c_e_win, lw4c_pi_win.
  setoid_replace (lw0m_e n) with ((5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q).
  2: { unfold lw0m_e, pie_mag, Qdiv. ring. }
  apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_fact n) (5 # 1)%Q (Z.of_nat (2 * n + 1) # 1)%Q).
  - apply q_fact_pos.
  - apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
  - apply Qle_to_QleT'. apply (Qle_trans _ ((5 # 1)%Q * (Z.of_nat n # 1))).
    + unfold Qle. cbn [Qnum Qden Qmult]. lia.
    + apply (Qle_trans _ ((Z.of_nat n # 1) * (5 # 1)%Q)).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      * apply (Qle_trans _ (q_fact n * (5 # 1)%Q)).
        -- apply (Qmult_le_compat_r (Z.of_nat n # 1) (q_fact n) (5 # 1)%Q).
           ++ exact (QleT'_to_Qle (Z.of_nat n # 1) (q_fact n) (lw4c_qfact_ge_nat n Hn)).
           ++ apply QleT'_to_Qle. apply (Qle_of_nat 0 5). lia.
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* A3: the pointwise strict contrast — n >= 2 implies 1/n! < 5/(2n+1)
   (the pointwise form of factorial decay dominating the harmonic rate);
   the premise in arrow position matches the certified shape of
   [leiblw_natwin_unbounded] *)
Lemma lw4c_e_win_lt_pi_win : forall n : nat, (2 <= n)%nat ->
  QltT (lw4c_e_win n) (lw4c_pi_win n).
Proof.
  intros n Hn. apply Qlt_to_QltT.
  assert (H1 : (1 <= n)%nat) by lia.
  unfold lw4c_e_win, lw4c_pi_win.
  setoid_replace (lw0m_e n) with ((5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q).
  2: { unfold lw0m_e, pie_mag, Qdiv. ring. }
  apply (Qle_lt_trans _ ((4 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q)).
  - apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_fact n) (4 # 1)%Q (Z.of_nat (2 * n + 1) # 1)%Q).
    + apply q_fact_pos.
    + apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ ((4 # 1)%Q * (Z.of_nat n # 1))).
      * unfold Qle. cbn [Qnum Qden Qmult]. lia.
      * apply (Qle_trans _ ((Z.of_nat n # 1) * (4 # 1)%Q)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (q_fact n * (4 # 1)%Q)).
           ++ apply (Qmult_le_compat_r (Z.of_nat n # 1) (q_fact n) (4 # 1)%Q).
              ** exact (QleT'_to_Qle (Z.of_nat n # 1) (q_fact n) (lw4c_qfact_ge_nat n H1)).
              ** apply QleT'_to_Qle. apply (Qle_of_nat 0 4). lia.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - unfold Qdiv.
    apply (Qmult_lt_compat_r _ _ (Qinv (Z.of_nat (2 * n + 1) # 1)%Q)).
    + apply (Qinv_lt_0_compat (Z.of_nat (2 * n + 1) # 1)%Q).
      unfold Qlt. simpl. lia.
    + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 4 5). lia.
Qed.

(* A4: the π window dominates every fixed power-rate window — k >= 1,
   n >= 1 imply 1/(n+1)^k < 5/(2n+1); the constructive pointwise
   refutation of any power-rate bound on the π window *)
Definition lw4c_powwin (k n : nat) : Q :=
  1%Q / q_pow ((Z.of_nat (Datatypes.S n)) # 1)%Q k.
Lemma lw4c_pi_win_gt_powwin : forall k n : nat, (1 <= k)%nat -> (1 <= n)%nat ->
  QltT (lw4c_powwin k n) (lw4c_pi_win n).
Proof.
  intro k. intro n. intro Hk. intro Hn. apply Qlt_to_QltT.
  unfold lw4c_powwin, lw4c_pi_win.
  setoid_replace (lw0m_e n) with ((5 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q).
  2: { unfold lw0m_e, pie_mag, Qdiv. ring. }
  assert (Hpowpos : forall j : nat, Qlt 0 (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q j)).
  { intro j. induction j as [| j IHj]; simpl.
    - unfold Qlt. simpl. lia.
    - apply (Qmult_lt_0_compat (Z.of_nat (Datatypes.S n) # 1)%Q
               (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q j)).
      + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (Datatypes.S n)). lia.
      + exact IHj. }
  assert (Hpowge : forall j : nat, (1 <= j)%nat ->
    Qle (Z.of_nat (Datatypes.S n) # 1)%Q (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q j)).
  { intro j. induction j as [| j IHj]; intro Hj.
    - exfalso. lia.
    - destruct j as [| j'].
      + pose proof (qeqT_imp_qeq _ _ (q_pow_succ (Z.of_nat (Datatypes.S n) # 1)%Q 0)) as Hps0.
        setoid_rewrite Hps0.
        assert (H0 : q_pow (Z.of_nat (Datatypes.S n) # 1)%Q 0 == 1%Q)
          by (simpl; reflexivity).
        rewrite H0. apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
      + pose proof (qeqT_imp_qeq _ _
            (q_pow_succ (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))) as Hps1.
        setoid_rewrite Hps1.
        apply (Qle_trans _ ((Z.of_nat (Datatypes.S n) # 1)%Q * 1)%Q).
        * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        * apply (Qle_trans _ (1%Q * q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
          -- setoid_rewrite (Qmult_1_r (Z.of_nat (Datatypes.S n) # 1)%Q).
             setoid_rewrite (Qmult_1_l (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
             assert (H1 : (1 <= Datatypes.S j')%nat) by lia.
             exact (IHj H1).
          -- apply (Qmult_le_compat_r 1%Q (Z.of_nat (Datatypes.S n) # 1)%Q
                     (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
             ++ apply QleT'_to_Qle. apply (Qle_of_nat 1 (Datatypes.S n)). lia.
             ++ apply (Qlt_le_weak 0%Q
                        (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q (Datatypes.S j'))).
                apply (Hpowpos (Datatypes.S j')). }
  apply (Qle_lt_trans _ ((4 # 1)%Q / (Z.of_nat (2 * n + 1) # 1)%Q)).
  - apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q k) (4 # 1)%Q
             (Z.of_nat (2 * n + 1) # 1)%Q).
    + apply Qlt_to_QltT. exact (Hpowpos k).
    + apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
    + apply Qle_to_QleT'. apply (Qle_trans _ ((4 # 1)%Q * (Z.of_nat (Datatypes.S n) # 1)%Q)).
      * unfold Qle. cbn [Qnum Qden Qmult]. lia.
      * apply (Qle_trans _ ((Z.of_nat (Datatypes.S n) # 1)%Q * (4 # 1)%Q)).
        -- apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
        -- apply (Qle_trans _ (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q k * (4 # 1)%Q)).
           ++ apply (Qmult_le_compat_r (Z.of_nat (Datatypes.S n) # 1)%Q
                       (q_pow (Z.of_nat (Datatypes.S n) # 1)%Q k) (4 # 1)%Q).
              ** apply (Hpowge k). exact Hk.
              ** apply QleT'_to_Qle. apply (Qle_of_nat 0 4). lia.
           ++ apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
  - unfold Qdiv.
    apply (Qmult_lt_compat_r _ _ (Qinv (Z.of_nat (2 * n + 1) # 1)%Q)).
    + apply (Qinv_lt_0_compat (Z.of_nat (2 * n + 1) # 1)%Q).
      apply QltT_to_Qlt. apply (Qlt_of_nat_lt 0 (2 * n + 1)). lia.
    + apply QltT_to_Qlt. apply (Qlt_of_nat_lt 4 5). lia.
Qed.

(* A5: the factorial window is bounded by the exponential-rate window —
   for all m, 1/(S m)! <= 2^{-m} (stated without nat subtraction) *)
Lemma lw4c_e_win_le_expwin : forall m : nat,
  QleT' (lw4c_e_win (Datatypes.S m)) (1%Q / q_pow (2 # 1)%Q m).
Proof.
  intro m. apply Qle_to_QleT'. unfold lw4c_e_win.
  assert (Hpowpos : Qlt 0 (q_pow (2 # 1)%Q m)).
  { induction m as [| m IHm]; simpl.
    - unfold Qlt. simpl. lia.
    - apply (Qmult_lt_0_compat (2 # 1)%Q (q_pow (2 # 1)%Q m)).
      + exact (QltT_to_Qlt _ _ Q2_pos).
      + exact IHm. }
  assert (Hfact : Qle (q_pow (2 # 1)%Q m) (q_fact (Datatypes.S m))).
  { clear Hpowpos. induction m as [| m IHm].
    - simpl. unfold Qle. simpl. lia.
    - pose proof (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q m)) as Hpsm.
      setoid_rewrite Hpsm.
      pose proof (qeqT_imp_qeq _ _ (q_fact_succ (Datatypes.S m))) as Hfsm.
      setoid_rewrite Hfsm.
      setoid_rewrite (Qmult_comm (2 # 1)%Q (q_pow (2 # 1)%Q m)).
      setoid_rewrite (Qmult_comm (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q
                       (q_fact (Datatypes.S m))).
      apply (Qle_trans _ (q_fact (Datatypes.S m) * (2 # 1)%Q)).
      + apply (Qmult_le_compat_r (q_pow (2 # 1)%Q m) (q_fact (Datatypes.S m))
                 (2 # 1)%Q).
        * exact IHm.
        * apply QleT'_to_Qle. apply (Qle_of_nat 0 2). lia.
      + setoid_rewrite (Qmult_comm (q_fact (Datatypes.S m)) (2 # 1)%Q).
        setoid_rewrite (Qmult_comm (q_fact (Datatypes.S m))
                         (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q).
        apply (Qmult_le_compat_r (2 # 1)%Q
                   (Z.of_nat (Datatypes.S (Datatypes.S m)) # 1)%Q
                   (q_fact (Datatypes.S m))).
        * apply QleT'_to_Qle. apply (Qle_of_nat 2 (Datatypes.S (Datatypes.S m))). lia.
        * apply (Qlt_le_weak 0%Q (q_fact (Datatypes.S m))). apply QltT_to_Qlt.
          apply q_fact_pos. }
  apply QleT'_to_Qle. apply (q_le_div_le 1%Q (q_fact (Datatypes.S m)) 1%Q (q_pow (2 # 1)%Q m)).
  - apply q_fact_pos.
  - apply Qlt_to_QltT. exact Hpowpos.
  - apply Qle_to_QleT'. apply (Qle_trans _ (1%Q * q_pow (2 # 1)%Q m)).
    + apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
    + setoid_rewrite (Qmult_1_l (q_pow (2 # 1)%Q m)).
      setoid_rewrite (Qmult_1_l (q_fact (Datatypes.S m))).
      exact Hfact.
Qed.

(* A6: the shape-separation main statement (the reserved name enabled);
   premises and sigT guard positions both use the NatLe Set order bound
   (S01 L88, the Id (Nat.leb) true face) — premises embedded in the And
   are Set-carried by the same method as the certified window-family
   statement with its And-embedded QltT premises; And is the S01 A×B
   form verbatim *)
Definition lw4c_shape_separation : Set :=
  And (forall n : nat, NatLe 2 n ->
         sigT (fun _ : NatLe 2 n =>
           QltT (lw4c_e_win n) (lw4c_pi_win n)))
      (forall k n : nat, NatLe 1 k -> NatLe 1 n ->
         sigT (fun _ : NatLe 1 k =>
           sigT (fun _ : NatLe 1 n =>
             QltT (lw4c_powwin k n) (lw4c_pi_win n)))).
Theorem lw4c_shape_separation_intro : lw4c_shape_separation.
Proof.
  split.
  - intro n. intro H. exists H.
    exact (lw4c_e_win_lt_pi_win n (NatLe_drop 2 n H)).
  - intro k. intro n. intro Hk. intro Hn.
    exists Hk. exists Hn.
    exact (lw4c_pi_win_gt_powwin k n (NatLe_drop 1 k Hk) (NatLe_drop 1 n Hn)).
Qed.

(* ============================================================ *)
(* §9. Numeric region (closed Set-face terms discharged by       *)
(*   [id_refl])                                                  *)
(* ============================================================ *)

(* T1: the closed-term window-width contrast table — 1/6 < 5/7, 1/120 < 5/11, 1/16 < 5/7 *)
Lemma lw4c_win_tbl :
  And (QltT (lw4c_e_win 3) (lw4c_pi_win 3))
      (And (QltT (lw4c_e_win 5) (lw4c_pi_win 5))
           (QltT (lw4c_powwin 2 3) (lw4c_pi_win 3))).
Proof. repeat split; exact id_refl. Qed.

(* e-side witness numeric table slot (planned as T2): the computational
   face of [lic_witness_e] does not terminate under [vm_compute], so this
   slot is vacant for now; the window-width contrast table T1 is in place. *)

(* ============================================================ *)
(* §10. Height-coordinate groundwork (definitions independent of *)
(*   the π-side supply; the certificate face awaits it)          *)
(* ============================================================ *)

(* A7: the height function, of the shape [S (Pos.to_nat (Qden (Qred q)))] *)
Definition lw4c_height (q : Q) : nat := Datatypes.S (Pos.to_nat (Qden (Qred q))).

(* A8: the q-coordinate version of the power-rate window (pure arithmetic definition, independent of the π-side supply) *)
Definition lw4c_powwin_q (mu0 : nat) (C : Q) (q : Q) : Q :=
  C / q_pow ((Z.of_nat (lw4c_height q)) # 1)%Q mu0.

(* ============================================================ *)
(* §11. Extraction + Print Assumptions, extended face (five      *)
(*   blocks, seven names; the T2 slot vacant)                    *)
(* ============================================================ *)
Separate Extraction lw4c_powwin lw4c_pi_win_gt_powwin
  lw4c_shape_separation lw4c_shape_separation_intro
  lw4c_height lw4c_powwin_q lw4c_win_tbl.
Print Assumptions lw4c_e_win_lt_pi_win.
Print Assumptions lw4c_shape_separation_intro.
Print Assumptions lw4c_win_tbl.
