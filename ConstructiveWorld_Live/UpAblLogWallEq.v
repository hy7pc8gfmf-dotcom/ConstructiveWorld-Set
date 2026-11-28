(* ======================================================================== *)
(*  UpAblLogWallEq.v - Minimal-station selector vs limited LPO: two-way     *)
(*  equivalence through the conditioned interface (Set-carrier completion). *)
(*  Mission. lgwe_equivalence : And (lgw_MinSel -> lgw_lpo_family)          *)
(*  (rLPO -> lgwe_MinSelC) completes the one-way reduction of UpAblLogWall. *)
(*  Forward arm: lgw_lpo_of_min_sel (reused). Backward arm                  *)
(*  lgwe_min_sel_of_rlpo builds the conditioned selector lgwe_MinSelC       *)
(*  from rLPO in three moves: station-gap dichotomy (lgwe_station_decide),  *)
(*  a forced-pass scan bound from mix_k_select (transferred by              *)
(*  lgwe_rpow_eq_tv), and lgwe_scan merging first pass with pointwise       *)
(*  refutations into lgw_min_sel_spec. The unconditioned interface is       *)
(*  constructively empty (lgwe_minsel_refutable : lgw_MinSel ->             *)
(*  Empty_set at kappa = TV0 = budget = real_one).                          *)
(*  Dependencies. Stdlib QArith (QArith.QArith, QArith.Qabs), Arith,        *)
(*  Extraction; S01_BaseRing (Set-level And/Or/NatLe), S02_CauchyComplete   *)
(*  (Real layer, QltT/QeqT/QleT' faces, bridges, real_*_proj),              *)
(*  S07_RealSetoidExpLog (RealSetoid.real_eq_mult_compat), UpTVDoeblin      *)
(*  (tv_rpow), UpReqLpoEquiv (rLPO, q_abs_congr, q_abs_neg_eq),             *)
(*  UpReqMixingTime (mix_k_select), UpAblLogWall (lgw_* faces, fwd arm).    *)
(*  References. Statement-lineage source: UpAblLogWallEq.v of the baseline  *)
(*  Main world (faces re-carried on Set); stdlib QArith/Arith; mathlib has  *)
(*  no constructive counterpart.                                            *)
(*  Constructivity. Statement faces are Set-carried only (sigT, Set-level   *)
(*  And/Or, QltT/QeqT/QleT', NatLe); no Prop statement face exists (the Q   *)
(*  order lemmas of stdlib appear only inside proofs); every proof ends     *)
(*  transparent Defined; no Qlt-embedded sigT; zero axioms, zero admits.    *)
(*  Build. rocq c -native-compiler no -q -Q <Set Live root> "" single shot. *)
(* ======================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs.
From Stdlib Require Import Arith.Arith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S07_RealSetoidExpLog.
Require Import UpTVDoeblin.
Require Import UpReqLpoEquiv.
Require Import UpReqMixingTime.
Require Import UpAblLogWall.

Local Open Scope Q_scope.

(* ======================================================================== *)
(* Part 0 - The station gap and its pointwise projection law                *)
(* ======================================================================== *)

(* Station gap: budget minus the scaled traffic kappa^j * TV0 (the Real     *)
(* subtraction written as plus of the opposite).                            *)
Definition lgwe_diff (kappa TV0 budget : Real) (j : nat) : Real :=
  real_plus budget (real_opp (real_mult (lgw_rpow kappa j) TV0)).

Lemma lgwe_diff_proj : forall (kappa TV0 budget : Real) (j n : nat),
  QeqT (projT1 (lgwe_diff kappa TV0 budget j) n)
       (projT1 budget n - projT1 (lgw_rpow kappa j) n * projT1 TV0 n).
Proof.
  intros kappa TV0 budget j n. unfold lgwe_diff.
  apply qeq_imp_qeqT.
  rewrite (qeqT_imp_qeq _ _
    (real_plus_proj budget (real_opp (real_mult (lgw_rpow kappa j) TV0)) n)).
  rewrite (qeqT_imp_qeq _ _
    (real_opp_proj (real_mult (lgw_rpow kappa j) TV0) n)).
  rewrite (qeqT_imp_qeq _ _ (real_mult_proj (lgw_rpow kappa j) TV0 n)).
  ring.
Defined.

(* a <= |a| in the decidable QleT' face (positive branch: Qabs_pos;         *)
(* nonpositive branch: q_abs_neg_eq plus Qopp_le_compat).                   *)
Lemma lgwe_q_le_abs : forall a : Q, QleT' a (Qabs a).
Proof.
  intros a.
  destruct (Qlt_le_dec 0 a) as [Hpos | Hneg].
  - apply Qle_to_QleT'.
    rewrite (Qabs_pos a (Qlt_le_weak _ _ Hpos)).
    apply Qle_refl.
  - apply Qle_to_QleT'.
    rewrite (qeqT_imp_qeq _ _ (q_abs_neg_eq a Hneg)).
    apply (Qle_trans a 0 (- a)).
    + exact Hneg.
    + apply (Qopp_le_compat a 0). exact Hneg.
Defined.

(* ======================================================================== *)
(* Part 1 - The unconditioned interface is constructively empty             *)
(* ======================================================================== *)

(* The power family at base real_one is pointwise 1 at every station.       *)
Lemma lgwe_rpow_one_proj : forall (k n : nat),
  QeqT (projT1 (lgw_rpow real_one k) n) 1.
Proof.
  intros k. induction k as [|k IH]; intros n.
  - apply lgw_one_proj.
  - cbn [lgw_rpow].
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _
      (real_mult_proj real_one (lgw_rpow real_one k) n)).
    rewrite (qeqT_imp_qeq _ _ (lgw_one_proj n)).
    rewrite (qeqT_imp_qeq _ _ (IH n)).
    reflexivity.
Defined.

(* At kappa = TV0 = budget = real_one the pointwise gap is 1 - 1 = 0, so    *)
(* the gap branch of any alleged minimal station self-contradicts.          *)
Theorem lgwe_minsel_refutable : lgw_MinSel -> Empty_set.
Proof.
  intros Hsel.
  destruct (Hsel real_one real_one real_one) as [k [Htk _]].
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps [Heps [N HN]]].
  assert (HNN : NatLe N N) by (apply (NatLe_lift _ _ (Nat.le_refl N))).
  specialize (HN N HNN).
  apply QltT_to_Qlt in HN. apply QltT_to_Qlt in Heps.
  assert (Hz : projT1 real_one N
               - projT1 (real_mult (lgw_rpow real_one k) real_one) N == 0).
  { rewrite (qeqT_imp_qeq _ _ (lgw_one_proj N)).
    rewrite (qeqT_imp_qeq _ _
      (real_mult_proj (lgw_rpow real_one k) real_one N)).
    rewrite (qeqT_imp_qeq _ _ (lgwe_rpow_one_proj k N)).
    rewrite (qeqT_imp_qeq _ _ (lgw_one_proj N)).
    reflexivity. }
  rewrite Hz in HN.
  destruct (Qlt_irrefl eps (Qlt_trans eps 0 eps HN Heps)).
Defined.

(* ======================================================================== *)
(* Part 2 - Power-family transfer bridge (lgw_rpow vs tv_rpow)              *)
(* ======================================================================== *)

Lemma lgwe_rpow_eq_tv : forall (a : Real) (j : nat),
  real_eq (lgw_rpow a j) (tv_rpow a j).
Proof.
  intros a j. induction j as [|j IH].
  - apply real_eq_refl.
  - cbn [lgw_rpow tv_rpow].
    apply (RealSetoid.real_eq_mult_compat a (lgw_rpow a j) a (tv_rpow a j)).
    + apply real_eq_refl.
    + exact IH.
Defined.

(* ======================================================================== *)
(* Part 3 - Station-test bridges (gap branch forward, zero-gap refutation)  *)
(* ======================================================================== *)

(* Gap branch: a positive gap at some depth is exactly the station test.    *)
Lemma lgwe_test_of_diff : forall (kappa TV0 budget : Real) (j : nat),
  real_lt real_zero (lgwe_diff kappa TV0 budget j) ->
  lgw_test kappa TV0 budget j.
Proof.
  intros kappa TV0 budget j Hlt.
  unfold real_lt in Hlt. destruct Hlt as [eps [Heps [N HN]]].
  unfold lgw_test. unfold real_lt.
  exists eps. split.
  - exact Heps.
  - exists N. intros n Hn. specialize (HN n Hn).
    apply QltT_to_Qlt in HN.
    rewrite (qeqT_imp_qeq _ _ (lgwe_diff_proj kappa TV0 budget j n)) in HN.
    assert (Hz : projT1 real_zero n == 0) by exact (Qeq_refl 0).
    rewrite Hz in HN.
    apply Qlt_to_QltT.
    rewrite (qeqT_imp_qeq _ _ (real_mult_proj (lgw_rpow kappa j) TV0 n)).
    assert (Hm : projT1 budget n - projT1 (lgw_rpow kappa j) n * projT1 TV0 n - 0
                 == projT1 budget n - projT1 (lgw_rpow kappa j) n * projT1 TV0 n) by ring.
    rewrite Hm in HN.
    exact HN.
Defined.

(* Zero-gap refutation: a uniform vanishing bound on the gap contradicts    *)
(* the gap branch of the station test (meet the two depths at their max).   *)
Lemma lgwe_test_refute_of_zero :
  forall (kappa TV0 budget : Real) (j : nat),
  (forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat, NatLe N n ->
      QltT (Qabs (projT1 (lgwe_diff kappa TV0 budget j) n)) eps)) ->
  lgw_test kappa TV0 budget j -> Empty_set.
Proof.
  intros kappa TV0 budget j Hz Htk.
  unfold lgw_test in Htk. unfold real_lt in Htk.
  destruct Htk as [eps0 [Heps0 [N0 HN0]]].
  destruct (Hz eps0 Heps0) as [N1 HN1].
  assert (Hm0 : NatLe N0 (Nat.max N0 N1))
    by (apply (NatLe_lift _ _ (Nat.le_max_l N0 N1))).
  assert (Hm1 : NatLe N1 (Nat.max N0 N1))
    by (apply (NatLe_lift _ _ (Nat.le_max_r N0 N1))).
  specialize (HN0 _ Hm0). specialize (HN1 _ Hm1).
  apply QltT_to_Qlt in HN0. apply QltT_to_Qlt in HN1.
  rewrite (qeqT_imp_qeq _ _
    (real_mult_proj (lgw_rpow kappa j) TV0 (Nat.max N0 N1))) in HN0.
  rewrite (qeqT_imp_qeq _ _
    (lgwe_diff_proj kappa TV0 budget j (Nat.max N0 N1))) in HN1.
  set (X := projT1 budget (Nat.max N0 N1)
            - projT1 (lgw_rpow kappa j) (Nat.max N0 N1)
              * projT1 TV0 (Nat.max N0 N1)) in *.
  assert (HX : X < eps0).
  { apply (Qle_lt_trans X (Qabs X) eps0).
    - apply QleT'_to_Qle. apply lgwe_q_le_abs.
    - exact HN1. }
  destruct (Qlt_irrefl eps0 (Qlt_trans _ _ _ HN0 HX)).
Defined.

(* ======================================================================== *)
(* Part 4 - Decidable station test (the substantive use of rLPO)            *)
(* ======================================================================== *)

Definition lgwe_station_dec (kappa TV0 budget : Real) (j : nat) : Set :=
  Or (lgw_test kappa TV0 budget j)
     (lgw_test kappa TV0 budget j -> Empty_set).

(* From rLPO and a pointwise nonnegative gap: the apartness branch yields   *)
(* the test (gap branch); the vanishing branch and the zero branch of the   *)
(* nonnegativity Or family both refute the test.                            *)
Theorem lgwe_station_decide :
  forall (kappa TV0 budget : Real) (j : nat),
  rLPO -> real_le real_zero (lgwe_diff kappa TV0 budget j) ->
  lgwe_station_dec kappa TV0 budget j.
Proof.
  intros kappa TV0 budget j Hrlpo Hnn.
  destruct (Hrlpo (lgwe_diff kappa TV0 budget j)) as [Hapart | Hzero].
  - (* Apartness branch: split the nonnegativity Or family. *)
    unfold real_le in Hnn. destruct Hnn as [Hge | Heq0].
    + apply inl. exact (lgwe_test_of_diff kappa TV0 budget j Hge).
    + (* Gap is pointwise zero while rLPO witnesses apartness: refute. *)
      apply inr. intros Htk.
      destruct Hapart as [c [Hc0 [Nc HNc]]].
      assert (Hzf : (forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall n : nat, NatLe N n ->
          QltT (Qabs (projT1 (lgwe_diff kappa TV0 budget j) n)) eps))).
      { intros eps Heps. destruct (Heq0 eps Heps) as [N HN].
        exists N. intros n Hn. specialize (HN n Hn).
        apply QltT_to_Qlt in HN.
        assert (Hz0 : projT1 real_zero n == 0) by exact (Qeq_refl 0).
        rewrite Hz0 in HN.
        assert (H1 : (0 - projT1 (lgwe_diff kappa TV0 budget j) n)%Q
                     == (- projT1 (lgwe_diff kappa TV0 budget j) n)%Q) by ring.
        rewrite (qeqT_imp_qeq _ _ (q_abs_congr _ _ H1)) in HN.
        rewrite (Qabs_opp (projT1 (lgwe_diff kappa TV0 budget j) n)) in HN.
        apply Qlt_to_QltT. exact HN. }
      exact (lgwe_test_refute_of_zero kappa TV0 budget j Hzf Htk).
  - (* Vanishing branch: refute without any order data. *)
    apply inr. exact (lgwe_test_refute_of_zero kappa TV0 budget j Hzero).
Defined.

(* ======================================================================== *)
(* Part 5 - Bounded linear scan over the station interval [0,m]             *)
(* ======================================================================== *)

(* Scan base: station 0 passing yields the minimal station 0 outright;      *)
(* station 0 blocked refutes the whole interval [0,0].                      *)
Lemma lgwe_scan_O : forall (kappa TV0 budget : Real),
  (forall j : nat, lgwe_station_dec kappa TV0 budget j) ->
  Or
    (sigT (fun k : nat => And (NatLe k 0%nat) (lgw_min_sel_spec kappa TV0 budget k)))
    (forall j : nat, NatLe j 0%nat -> lgw_test kappa TV0 budget j -> Empty_set).
Proof.
  intros kappa TV0 budget Hdec.
  destruct (Hdec 0%nat) as [Hpass | Href].
  - apply inl. exists 0%nat. split.
    + apply (NatLe_lift _ _ (Nat.le_refl 0%nat)).
    + split.
      * exact Hpass.
      * intros j Hj _.
        assert (Hd : (Datatypes.S j <= 0)%nat) by (apply NatLe_drop; exact Hj).
        assert (HF : False) by exact (Nat.nle_succ_0 j Hd).
        destruct HF.
  - apply inr. intros j Hj Htj.
    assert (Hd : (j <= 0)%nat) by (apply NatLe_drop; exact Hj).
    assert (Hj0 : j = 0%nat) by exact (proj1 (Nat.le_0_r j) Hd).
    rewrite Hj0 in Htj. apply Href. exact Htj.
Defined.

(* Scan step: if the prefix [0,m'] is decided, a passing station carries    *)
(* the widened bound; all blocked merges the verdict on station S m'.       *)
Lemma lgwe_scan_S : forall (kappa TV0 budget : Real) (m' : nat),
  (forall j : nat, lgwe_station_dec kappa TV0 budget j) ->
  Or
    (sigT (fun k : nat => And (NatLe k m') (lgw_min_sel_spec kappa TV0 budget k)))
    (forall j : nat, NatLe j m' -> lgw_test kappa TV0 budget j -> Empty_set) ->
  Or
    (sigT (fun k : nat => And (NatLe k (Datatypes.S m')) (lgw_min_sel_spec kappa TV0 budget k)))
    (forall j : nat, NatLe j (Datatypes.S m') -> lgw_test kappa TV0 budget j -> Empty_set).
Proof.
  intros kappa TV0 budget m' Hdec Hscan.
  destruct Hscan as [[k [Hk Hspec]] | Hall].
  - apply inl. exists k. split.
    + assert (Hd : (k <= m')%nat) by (apply NatLe_drop; exact Hk).
      apply (NatLe_lift _ _ (Nat.le_le_succ_r _ _ Hd)).
    + exact Hspec.
  - destruct (Hdec (Datatypes.S m')) as [Hpass | Href].
    + apply inl. exists (Datatypes.S m'). split.
      * apply (NatLe_lift _ _ (Nat.le_refl (Datatypes.S m'))).
      * split.
        -- exact Hpass.
        -- intros j Hj Htj.
           apply (Hall j).
           ++ assert (Hd : (Datatypes.S j <= Datatypes.S m')%nat)
                by (apply NatLe_drop; exact Hj).
              apply (NatLe_lift _ _ (proj2 (Nat.succ_le_mono j m') Hd)).
           ++ exact Htj.
    + apply inr. intros j Hj Htj.
      destruct (Nat.leb j m') eqn:Elb.
      * (* j <= m': the prefix refutation carries. *)
        apply (Hall j).
        -- apply NatLe_lift. exact (proj1 (Nat.leb_le j m') Elb).
        -- exact Htj.
      * (* m' < j and j <= S m' force j = S m': this station's refutation. *)
        apply (proj1 (Nat.leb_gt j m')) in Elb.
        assert (Hd : (j <= Datatypes.S m')%nat) by (apply NatLe_drop; exact Hj).
        assert (Heq : j = Datatypes.S m')
          by exact (Nat.le_antisymm j (Datatypes.S m') Hd Elb).
        rewrite Heq in Htj. apply Href. exact Htj.
Defined.

Fixpoint lgwe_scan (kappa TV0 budget : Real)
  (Hdec : forall j : nat, lgwe_station_dec kappa TV0 budget j) (m : nat)
  : Or
      (sigT (fun k : nat => And (NatLe k m) (lgw_min_sel_spec kappa TV0 budget k)))
      (forall j : nat, NatLe j m -> lgw_test kappa TV0 budget j -> Empty_set) :=
  match m with
  | O => lgwe_scan_O kappa TV0 budget Hdec
  | Datatypes.S m' =>
      lgwe_scan_S kappa TV0 budget m' Hdec (lgwe_scan kappa TV0 budget Hdec m')
  end.

(* ======================================================================== *)
(* Part 6 - Backward arm (conditioned selector from rLPO)                   *)
(* ======================================================================== *)

(* Conditioned selector interface: the four positivity premises of          *)
(* mix_k_select plus the pointwise nonnegativity Or family per station.     *)
Definition lgwe_MinSelC : Set :=
  forall kappa TV0 budget : Real,
    real_lt real_zero kappa -> real_lt kappa real_one ->
    real_le real_zero TV0 -> real_lt real_zero budget ->
    (forall j : nat, real_le real_zero (lgwe_diff kappa TV0 budget j)) ->
    sigT (fun k : nat => lgw_min_sel_spec kappa TV0 budget k).

Theorem lgwe_min_sel_of_rlpo : rLPO -> lgwe_MinSelC.
Proof.
  intros Hrlpo kappa TV0 budget Hk1 Hk2 Ha Hb Hnn.
  (* Forced-pass upper bound: mix_k_select (tv_rpow face), transferred. *)
  destruct (mix_k_select kappa TV0 budget Hk1 Hk2 Ha Hb) as [kp Hmix].
  assert (Hpass : lgw_test kappa TV0 budget kp).
  { unfold lgw_test.
    apply (real_eq_lt_lt (real_mult (lgw_rpow kappa kp) TV0)
                         (real_mult (tv_rpow kappa kp) TV0) budget).
    - apply (RealSetoid.real_eq_mult_compat (lgw_rpow kappa kp) TV0
                (tv_rpow kappa kp) TV0).
      + exact (lgwe_rpow_eq_tv kappa kp).
      + apply real_eq_refl.
    - exact Hmix. }
  (* Per-station decidable tests (rLPO is consumed by lgwe_station_decide). *)
  assert (Hdec : forall j : nat, lgwe_station_dec kappa TV0 budget j).
  { intros j. apply lgwe_station_decide.
    - exact Hrlpo.
    - exact (Hnn j). }
  (* Linear sweep of [0,kp] and two-arm merge. *)
  destruct (lgwe_scan kappa TV0 budget Hdec kp) as [[k [Hk Hspec]] | Hall].
  - exists k. exact Hspec.
  - assert (Hkk : NatLe kp kp) by (apply (NatLe_lift _ _ (Nat.le_refl kp))).
    destruct (Hall kp Hkk Hpass).
Defined.

(* ======================================================================== *)
(* Part 7 - The two-way equivalence                                         *)
(* ======================================================================== *)

Theorem lgwe_equivalence :
  And (lgw_MinSel -> lgw_lpo_family) (rLPO -> lgwe_MinSelC).
Proof.
  split.
  - exact lgw_lpo_of_min_sel.
  - exact lgwe_min_sel_of_rlpo.
Defined.

(* ======================================================================== *)
(* Part 8 - Assumption audit and extraction face                            *)
(* ======================================================================== *)

Print Assumptions lgwe_diff_proj.
Print Assumptions lgwe_q_le_abs.
Print Assumptions lgwe_rpow_one_proj.
Print Assumptions lgwe_minsel_refutable.
Print Assumptions lgwe_rpow_eq_tv.
Print Assumptions lgwe_test_of_diff.
Print Assumptions lgwe_test_refute_of_zero.
Print Assumptions lgwe_station_decide.
Print Assumptions lgwe_scan_O.
Print Assumptions lgwe_scan_S.
Print Assumptions lgwe_scan.
Print Assumptions lgwe_min_sel_of_rlpo.
Print Assumptions lgwe_equivalence.

Separate Extraction lgwe_diff lgwe_station_dec lgwe_MinSelC.
