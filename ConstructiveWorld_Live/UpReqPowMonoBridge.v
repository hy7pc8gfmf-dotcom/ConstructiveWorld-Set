(* ConstructiveWorld-Set — le_b order-preserving multiplication closures (nonnegative-factor synthesizers). *)
(** * UpReqPowMonoBridge: the [le_b] multiplication-monotonicity closure synthesizer family.

    Mission.  Completes the missing piece of the synthesis chain behind the GeomIter
      conclusion I4 ("t ≤ t1 ⟹ KL_{t1} ≤_B κ^t·KL_0"): the [le_b] multiplication
      closure a ≤_B b ∧ 0 ≤ c ⟹ a·c ≤_B b·c.  A per-eps proof sticks at multiplying a
      strict order by a factor known only in B form — B-form 0 ≤_B c does not give the
      Or-form 0 ≤ c (constructively distinct; the one-way bridge [x3d_le_nonneg_or_to_b]).
      Pieces: [x3d_e0_key_lt] (the reciprocal-compression strict bound (w·inv(D))·M < w);
      [x3d_le_b_mult_r_nonneg_or] (the main synthesizer, Or-form nonnegative factor);
      [x3d_le_b_mult_l_nonneg_or] (the left-factor form); [x3d_le_b_mult_r_pos] (the
      strict-factor contrast alias of [leb3_le_b_pos_scale]); [x3d_le_nonneg_or_to_b]
      (the Or⟹B bridge); [x3d_le_b_mult_r_nonneg_bnd] (the bounded version
      a ≤_B b ∧ 0≤c ∧ c≤M, witness e₀ := eps·inv(M+1) — the theorization of the I4 upper-bound-material condition).

    Dependencies.  Stdlib [PeanoNat]; requires [S01_BaseRing] through [S15_TailFEPUp],
      [UpRealLeB], [UpRealLeB2], [UpRealLeB3] of this development.

    References.  [real_le_closure_b_nonneg] (the Or-form nonnegative finisher of
      UpRealLeB2); the Or-form multiplication-monotonicity trio of S07 ([real_le_mult_compat_weak],
      [real_le_mult_compat_r], [RealSetoid.real_lt_le_iff_req]); the source brief is the
      endnote of [UpReqGeomIter.v] (conclusion I4); the companion composition lives in the
      use-side file [_x3d_I4BridgeCheck.v].

    Constructivity.  Purely constructive, nothing admitted (all [Qed]); statements
      [Set]-valued; pure term-mode assembly.  The unbounded B-form-factor version remains an
      explicit assumption (the B⟹Or conversion is constructively unavailable).

    Build.  [coqc -native-compiler no -q -Q ConstructiveWorld_Live "" UpReqPowMonoBridge.v]
      compiles cleanly (exit 0); the artifact's first eight bytes are [436f7121 000160bc]. *)

From Stdlib Require Import PeanoNat.
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
Require Import UpRealLeB.
Require Import UpRealLeB2.
Require Import UpRealLeB3.

(* ============================================================ *)
(* 0. The reciprocal-compression strict bound engine             *)
(* ============================================================ *)

(* Piece 0: (w·inv(D))·M < w under M < D, D > 0, w > 0.
   Chain: inv(D)·M < inv(D)·D == 1 (two hops of strict multiplication
   monotonicity) implies w·(inv(D)·M) < w·1 == w (strict preservation by
   the positive left factor w), finished by an associative reshaping. *)
Lemma x3d_e0_key_lt : forall (w M : Real)
    (HMlt1 : real_lt M (real_plus M real_one))
    (HMp : real_lt real_zero (real_plus M real_one))
    (Hw : real_lt real_zero w),
  real_lt
    (real_mult (real_mult w (real_inv_pos (real_plus M real_one) HMp)) M)
    w.
Proof.
  intros w M HMlt1 HMp Hw.
  assert (HiD : real_lt real_zero
                  (real_inv_pos (real_plus M real_one) HMp))
    by exact (real_inv_pos_pos (real_plus M real_one) HMp).
  (* hop 1: M·inv(D) < (M+1)·inv(D) (M < M+1, inv(D) > 0), after commutativity reshaping *)
  assert (Hs1 : real_lt (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
                  (real_mult (real_inv_pos (real_plus M real_one) HMp)
                     (real_plus M real_one))).
  { exact (RealSetoid.real_lt_compat
             (real_mult M (real_inv_pos (real_plus M real_one) HMp))
             (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
             (real_mult (real_plus M real_one)
                (real_inv_pos (real_plus M real_one) HMp))
             (real_mult (real_inv_pos (real_plus M real_one) HMp)
                (real_plus M real_one))
             (real_mult_comm M (real_inv_pos (real_plus M real_one) HMp))
             (real_mult_comm (real_plus M real_one)
                (real_inv_pos (real_plus M real_one) HMp))
             (real_mult_lt_compat M (real_plus M real_one)
                (real_inv_pos (real_plus M real_one) HMp) HMlt1 HiD)). }
  (* hop 2: the right side inv(D)·(M+1) == 1 normalizes (first by commutativity to the D·inv(D) form), giving inv(D)·M < 1 *)
  assert (Hs2 : real_lt (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
                  real_one).
  { exact (RealSetoid.real_lt_id_r
             (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
             (real_mult (real_inv_pos (real_plus M real_one) HMp)
                (real_plus M real_one))
             real_one
             (real_eq_trans
                (real_mult (real_inv_pos (real_plus M real_one) HMp)
                   (real_plus M real_one))
                (real_mult (real_plus M real_one)
                   (real_inv_pos (real_plus M real_one) HMp))
                real_one
                (real_mult_comm (real_inv_pos (real_plus M real_one) HMp)
                   (real_plus M real_one))
                (real_inv_pos_correct (real_plus M real_one) HMp))
             Hs1). }
  (* hop 3: multiplication by w > 0 preserves strict order, w·(inv(D)·M) < w·1 *)
  assert (Hs3 : real_lt (real_mult w
                   (real_mult (real_inv_pos (real_plus M real_one) HMp) M))
                  (real_mult w real_one))
    by exact (real_mult_lt_compat_l
                (real_mult (real_inv_pos (real_plus M real_one) HMp) M)
                real_one w Hs2 Hw).
  (* finish: associative reshaping plus the normalization w·1 == w *)
  exact (RealSetoid.real_lt_id_l
           (real_mult (real_mult w
              (real_inv_pos (real_plus M real_one) HMp)) M)
           (real_mult w
              (real_mult (real_inv_pos (real_plus M real_one) HMp) M))
           w
           (real_eq_sym _ _
              (real_mult_assoc w
                 (real_inv_pos (real_plus M real_one) HMp) M))
           (RealSetoid.real_lt_id_r
              (real_mult w
                 (real_mult (real_inv_pos (real_plus M real_one) HMp) M))
              (real_mult w real_one) w (real_mult_one w) Hs3)).
Qed.

(* ============================================================ *)
(* 1. The main synthesizer: le_b multiplication monotonicity for *)
(*   an Or-form nonnegative right factor                         *)
(* ============================================================ *)

(* Piece 1: a ≤_B b and 0 ≤ c (Or form) give a·c ≤_B b·c.  The finisher is applied
   in reverse (C := c; Or-form nonnegativity suffices): given e > 0 it is enough to
   produce the Or form a·c ≤ b·c + c·e — from a < b+e, the lt-to-Or conversion and
   weak monotonicity in the nonnegative right factor give a·c ≤ (b+e)·c, and
   (b+e)·c == b·c + c·e completes it by a distributive reshaping. *)
Lemma x3d_le_b_mult_r_nonneg_or : forall a b c : Real,
  real_le_b a b -> real_le real_zero c ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c H Hc.
  apply (real_le_closure_b_nonneg (real_mult a c) (real_mult b c) c Hc).
  intros eps Heps. unfold real_le.
  assert (Hdist : real_eq (real_mult (real_plus b eps) c)
                    (real_plus (real_mult b c) (real_mult c eps))).
  { apply (real_eq_trans _ (real_mult c (real_plus b eps)) _).
    - apply real_mult_comm.
    - apply (real_eq_trans _
               (real_plus (real_mult c b) (real_mult c eps)) _).
      + apply real_distrib.
      + apply (RealSetoid.real_eq_plus_compat (real_mult c b)
                 (real_mult c eps) (real_mult b c) (real_mult c eps)).
        * apply real_mult_comm.
        * apply real_eq_refl. }
  exact (RealSetoid.real_le_id_r (real_mult a c)
           (real_mult (real_plus b eps) c)
           (real_plus (real_mult b c) (real_mult c eps))
           Hdist
           (real_le_mult_compat_weak a (real_plus b eps) c Hc
              (RealSetoid.real_lt_le_iff_req a (real_plus b eps)
                 (inl (H eps Heps))))).
Qed.

(* Piece 2: the left-factor form (the c·a ≤_B c·b direction), transported from piece 1 by two commutativity steps *)
Lemma x3d_le_b_mult_l_nonneg_or : forall a b c : Real,
  real_le_b a b -> real_le real_zero c ->
  real_le_b (real_mult c a) (real_mult c b).
Proof.
  intros a b c H Hc.
  apply (leb3_le_b_eq_l (real_mult a c) (real_mult c a) (real_mult c b)).
  - apply real_mult_comm.
  - apply (leb3_le_b_eq_r (real_mult a c) (real_mult b c) (real_mult c b)).
    + exact (x3d_le_b_mult_r_nonneg_or a b c H Hc).
    + apply real_mult_comm.
Qed.

(* ============================================================ *)
(* 2. The contrast anchor and the interface-face documentation pieces *)
(* ============================================================ *)

(* Piece 3: the strict-factor contrast form (the 0 < c version) — a signature-aligned
   alias of [leb3_le_b_pos_scale] (UpRealLeB3 piece 6; the original proof is reused
   verbatim).  It anchors the strict face of the three-form contrast. *)
Lemma x3d_le_b_mult_r_pos : forall a b c : Real,
  real_le_b a b -> real_lt real_zero c ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c H Hc.
  exact (leb3_le_b_pos_scale a b c H Hc).
Qed.

(* Piece 4: the one-way bridge for the nonnegativity certificate — the Or form 0≤c
   gives the B form 0 ≤_B c.  The reverse (B⟹Or) is constructively unavailable: if
   the factor is known only in B form this bridge does not apply — precisely the
   position of the explicit assumption named by conclusion I4 (piece 5 routes
   around it with a bounded upper bound M, below). *)
Lemma x3d_le_nonneg_or_to_b : forall c : Real,
  real_le real_zero c -> real_le_b real_zero c.
Proof.
  intro c. apply real_le_to_le_b.
Qed.

(* ============================================================ *)
(* 3. The bounded nonnegative-right-factor version (the          *)
(*   theorization of the upper-bound-material condition of       *)
(*   conclusion I4): a ≤_B b ∧ 0≤c ∧ c≤M gives a·c ≤_B b·c, by a *)
(*   direct per-eps proof with the witness e₀ := eps·inv(M+1):   *)
(*   from a < b+e₀, after multiplying out, e₀·c ≤ e₀·M < eps     *)
(*   (the piece-0 engine) — the surplus is pressed back below eps. *)
(* ============================================================ *)
Lemma x3d_le_b_mult_r_nonneg_bnd : forall a b c M : Real,
  real_le_b a b -> real_le real_zero c -> real_le c M ->
  real_le_b (real_mult a c) (real_mult b c).
Proof.
  intros a b c M H Hc0 HCm. unfold real_le_b. intros eps Heps.
  assert (HMle0 : real_le real_zero M)
    by exact (real_le_trans real_zero c M Hc0 HCm).
  assert (HMlt1 : real_lt M (real_plus M real_one)).
  { apply (RealSetoid.real_lt_id_l M (real_plus M real_zero)
             (real_plus M real_one)).
    - apply real_eq_sym. apply real_plus_zero.
    - apply (real_lt_plus_translate M real_zero real_one).
      exact real_lt_zero_one. }
  assert (HMp : real_lt real_zero (real_plus M real_one)).
  { apply (real_lt_le_trans real_zero real_one (real_plus M real_one)
             real_lt_zero_one).
    apply (RealSetoid.real_le_id_l real_one (real_plus real_zero real_one)
             (real_plus M real_one)).
    - apply real_eq_sym. apply real_plus_comm.
    - apply (real_le_plus_compat real_zero M real_one real_one).
      + exact HMle0.
      + apply real_le_refl. }
  (* the witness e₀ := eps·inv(M+1) > 0 and the piece-0 key bound e₀·M < eps *)
  assert (HinvMp : real_lt real_zero
    (real_inv_pos (real_plus M real_one) HMp))
    by exact (real_inv_pos_pos (real_plus M real_one) HMp).
  assert (He0pos : real_lt real_zero
    (real_mult eps (real_inv_pos (real_plus M real_one) HMp)))
    by exact (real_mult_positive eps
                (real_inv_pos (real_plus M real_one) HMp) Heps HinvMp).
  assert (Hkey : real_lt
    (real_mult (real_mult eps (real_inv_pos (real_plus M real_one) HMp)) M)
    eps)
    by exact (x3d_e0_key_lt eps M HMlt1 HMp Heps).
  (* the Or-form chain: a ≤ b+e₀ implies a·c ≤ (b+e₀)·c (weak monotonicity in the nonnegative right factor) *)
  assert (Hmono1 : real_le (real_mult a c)
                     (real_mult (real_plus b
                        (real_mult eps
                           (real_inv_pos (real_plus M real_one) HMp))) c))
    by exact (real_le_mult_compat_weak a
                (real_plus b
                   (real_mult eps
                      (real_inv_pos (real_plus M real_one) HMp))) c Hc0
                (RealSetoid.real_lt_le_iff_req a
                   (real_plus b
                      (real_mult eps
                         (real_inv_pos (real_plus M real_one) HMp)))
                   (inl (H (real_mult eps
                          (real_inv_pos (real_plus M real_one) HMp))
                          He0pos)))).
  (* distributive reshaping: (b+e₀)·c == b·c + e₀·c (comm, then left distributivity, then a compatibility reordering) *)
  assert (Hdist : real_eq
    (real_mult (real_plus b
       (real_mult eps (real_inv_pos (real_plus M real_one) HMp))) c)
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) c))).
  { apply (real_eq_trans _
             (real_mult c
                (real_plus b
                   (real_mult eps
                      (real_inv_pos (real_plus M real_one) HMp)))) _).
    - apply real_mult_comm.
    - apply (real_eq_trans _
               (real_plus (real_mult c b)
                  (real_mult c
                     (real_mult eps
                        (real_inv_pos (real_plus M real_one) HMp)))) _).
      + apply real_distrib.
      + apply (RealSetoid.real_eq_plus_compat (real_mult c b)
                 (real_mult c
                    (real_mult eps
                       (real_inv_pos (real_plus M real_one) HMp)))
                 (real_mult b c)
                 (real_mult (real_mult eps
                    (real_inv_pos (real_plus M real_one) HMp)) c)).
        * apply real_mult_comm.
        * apply real_mult_comm. }
  assert (Hmid1 : real_le (real_mult a c)
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) c)))
    by exact (RealSetoid.real_le_id_r (real_mult a c) _ _ Hdist Hmono1).
  (* e₀·c ≤ e₀·M (monotonicity in the nonnegative left factor: e₀ > 0, c ≤ M) *)
  assert (Hmono2 : real_le
    (real_mult (real_mult eps (real_inv_pos (real_plus M real_one) HMp)) c)
    (real_mult (real_mult eps (real_inv_pos (real_plus M real_one) HMp)) M))
    by exact (real_le_mult_compat_r
                (real_mult eps (real_inv_pos (real_plus M real_one) HMp))
                c M
                (RealSetoid.real_lt_le_iff_req real_zero _
                   (inl He0pos)) HCm).
  assert (Hmid2 : real_le
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) c))
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) M)))
    by exact (real_le_plus_compat (real_mult b c) (real_mult b c) _ _
                (real_le_refl (real_mult b c)) Hmono2).
  assert (Hmid3 : real_le (real_mult a c)
    (real_plus (real_mult b c)
       (real_mult (real_mult eps
          (real_inv_pos (real_plus M real_one) HMp)) M)))
    by exact (real_le_trans _ _ _ Hmid1 Hmid2).
  exact (real_le_lt_trans _ _
           (real_plus (real_mult b c) eps) Hmid3
           (real_lt_plus_translate (real_mult b c) _
             eps Hkey)).
Qed.

(* ============================================================ *)
(* 4. Assumption audit (all Closed; the evidence is in the compile log) *)
(* ============================================================ *)

Print Assumptions x3d_e0_key_lt.
Print Assumptions x3d_le_b_mult_r_nonneg_or.
Print Assumptions x3d_le_b_mult_l_nonneg_or.
Print Assumptions x3d_le_b_mult_r_pos.
Print Assumptions x3d_le_nonneg_or_to_b.
Print Assumptions x3d_le_b_mult_r_nonneg_bnd.

(* ============================================================ *)
(* Endnote: the honest registration table                        *)

(*   The B-form-factor-with-upper-bound face (piece 5) theorizes the upper-bound
   material named by conclusion I4; the composition closure of the powb
   monotonicity and GeomIter companion pieces is completed in the use-side
   verification file [_x3d_I4BridgeCheck.v]: with [Hkl0or] (the Or-form KL_0
   nonnegativity certificate) in place, the chain "t ≤ t1 ⟹ KL_{t1} ≤_B
   κ^t·KL_0" closes fully.  The unbounded piece with a factor known only in B
   form remains an explicit assumption — the blocker is exactly the B⟹Or
   conversion position (the reverse of piece 4). *)
(* ============================================================ *)
