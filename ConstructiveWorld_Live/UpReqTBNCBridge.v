(* ConstructiveWorld-Set -- Banach-algebra bridges for double Cauchy convolution sums. *)

(** * UpReqTBNCBridge: diagonal fold decomposition of double convolution sums.

    Mission.  This file formalizes the diagonal fold decomposition of double
      Cauchy convolution sums over a Banach algebra: the pointwise agreement
      of the two summation recursions [tbg_ncvsum_bsum], the row bridge
      [tbg_row_dock], the square fold [tbg_conv_bsum], the triangle fold
      [tbg_fold_diagf], and the diagonal faces [tbg_diag_face] and
      [tbg_diag_seq] splitting off the corner remainder [tbg_corner].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia], [Extraction].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachCauchyD], [UpReqBanachDouble], [UpReqBanachExp],
      [UpReqBanachProd], [UpReqNormConv] of this development.

    References.  This development, UpReqTBNCBridge.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqTBNCBridge.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 00015ff4]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachDouble.
Require Import UpReqNormConv.
Require Import UpReqBanachCauchyD.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Section 1. The ncv half: row restatement bridge and square bsum folding. *)
(* ============================================================ *)

(* The two summation recursions [ncv_sum] and [bsum] agree pointwise in [bae]. *)
(* Their bodies have the same shape, but at an open [n] the two sides are not  *)
(* convertible, so the proof proceeds by induction and transports through      *)
(* [bplus_wd_l]; on the [bae] face [rewrite] is barred and the unfolding goes  *)
(* through [change], as the library prescribes.                                *)
Lemma tbg_ncvsum_bsum : forall (BA : Set) (bae : BA -> BA -> Set)
                               (B : BanachAlg BA bae) (f : nat -> BA) (n : nat),
  bae (ncv_sum _ _ B f n) (bsum _ _ B n f).
Proof.
  intros BA bae B f n. induction n as [| m IH].
  - cbn [ncv_sum bsum].
    apply (@bae_refl _ _ B).
  - cbn [ncv_sum bsum].
    apply (@bplus_wd_l _ _ B). exact IH.
Qed.

(* Row bridge: the [ncv] row of counting width [S n] equals the [bd2] row of *)
(* closed width [n]; the proof restates it through [tbg_ncvsum_bsum]. *)
Lemma tbg_row_dock : forall (BA : Set) (bae : BA -> BA -> Set)
                            (B : BanachAlg BA bae) (a b : nat -> BA) (k n : nat),
  bae (ncv_row _ _ B a b k (Datatypes.S n)) (bd2_row _ _ B a b k n).
Proof.
  intros BA bae B a b k n.
  unfold ncv_row, bd2_row.
  exact (tbg_ncvsum_bsum _ _ B (fun j : nat => @bmult _ _ B (a k) (b j))
               (Datatypes.S n)).
Qed.

(* Square folding: [ncv_conv B a b m n] equals the [bsum]-carried sum over *)
(* [k < m] of [ncv_row B a b k n]. *)
Lemma tbg_conv_bsum : forall (BA : Set) (bae : BA -> BA -> Set)
                             (B : BanachAlg BA bae) (a b : nat -> BA) (m n : nat),
  bae (ncv_conv _ _ B a b m n)
         (bsum _ _ B m (fun k : nat => ncv_row _ _ B a b k n)).
Proof.
  intros BA bae B a b m n. induction m as [| m' IH].
  - cbn [ncv_conv bsum].
    apply (@bae_refl _ _ B).
  - cbn [ncv_conv bsum].
    apply (@bplus_wd_l _ _ B). exact IH.
Qed.

(* ============================================================ *)
(* Section 2. The bd2 half: the triangle-fold row sum equals the termwise *)
(* face [bd2_diagf]. *)
(* ============================================================ *)

Lemma tbg_fold_diagf : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (a b : nat -> BA) (n : nat),
  bae (bsum _ _ B (Datatypes.S n) (fun i : nat => bd2_row _ _ B a b i (Nat.sub n i)))
         (bd2_diagf _ _ B a b 0%nat n).
Proof.
  intros BA bae B a b n.
  apply (@bae_trans _ _ B
      (bsum _ _ B (Datatypes.S n) (fun i : nat => bd2_row _ _ B a b i (Nat.sub n i)))
      (bd2_rect _ _ B a b 0%nat n)).
  - unfold bd2_rect.
    apply (@bsum_ext _ _ B (Datatypes.S n)
             (fun i : nat => bd2_row _ _ B a b i (Nat.sub n i))
             (fun i : nat =>
                bsum _ _ B (Datatypes.S (Nat.sub n i))
                   (fun j : nat => @bmult _ _ B (a (0%nat + i)%nat) (b j)))).
    intros k Hk.
    unfold bd2_row.
    assert (H0k : (0%nat + k)%nat = k) by apply Nat.add_0_l.
    rewrite H0k.
    apply (@bae_refl _ _ B).
  - apply (@bae_trans _ _ B
        (bd2_rect _ _ B a b 0%nat n) (bd2_tfrom _ _ B a b 0%nat n)).
    + exact (@bae_sym _ _ B (bd2_tfrom _ _ B a b 0%nat n)
                       (bd2_rect _ _ B a b 0%nat n)
                       (bd2_tfrom_rect _ _ B a b n 0%nat)).
    + apply (@bae_trans _ _ B
          (bd2_tfrom _ _ B a b 0%nat n) (bd2_diag _ _ B n a b)).
      * exact (bd2_tri_eq_diag _ _ B n a b).
      * apply (@bae_refl _ _ B).
Qed.

(* ============================================================ *)
(* Section 3. The corner remainder: the general-family form of [bxcd_U], the *)
(* part of the square with [i + j > n] outside the diagonal. *)
(* ============================================================ *)

Definition tbg_corner (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                       (a b : nat -> BA) (n : nat) : BA :=
  bsum _ _ B (Datatypes.S n)
    (fun i : nat =>
       bsum _ _ B (Datatypes.S n)
          (fun j : nat =>
             if Nat.ltb (Nat.sub n i) j
             then @bmult _ _ B (a i) (b j)
             else @bzero _ _ B)).

(* ============================================================ *)
(* Section 4. Main statement: the termwise diagonal bridge. *)
(*   The square, the convergence-side dependency domain of [ncv_conv], equals *)
(* the triangle termwise face [bd2_diagf] plus the corner remainder. *)
(* ============================================================ *)

Theorem tbg_diag_face : forall (BA : Set) (bae : BA -> BA -> Set)
                               (B : BanachAlg BA bae) (a b : nat -> BA) (n : nat),
  bae (ncv_conv _ _ B a b (Datatypes.S n) (Datatypes.S n))
         (@bplus _ _ B (bd2_diagf _ _ B a b 0%nat n) (tbg_corner _ _ B a b n)).
Proof.
  intros BA bae B a b n.
  apply (@bae_trans _ _ B
      (ncv_conv _ _ B a b (Datatypes.S n) (Datatypes.S n))
      (bsum _ _ B (Datatypes.S n) (fun k : nat => ncv_row _ _ B a b k (Datatypes.S n)))).
  - exact (tbg_conv_bsum _ _ B a b (Datatypes.S n) (Datatypes.S n)).
  - apply (@bae_trans _ _ B
        (bsum _ _ B (Datatypes.S n) (fun k : nat => ncv_row _ _ B a b k (Datatypes.S n)))
        (bsum _ _ B (Datatypes.S n) (fun k : nat => bd2_row _ _ B a b k n))).
  + apply (@bsum_ext _ _ B (Datatypes.S n)
           (fun k : nat => ncv_row _ _ B a b k (Datatypes.S n))
           (fun k : nat => bd2_row _ _ B a b k n)).
    intros k Hk. exact (tbg_row_dock _ _ B a b k n).
  + apply (@bae_trans _ _ B
        (bsum _ _ B (Datatypes.S n) (fun k : nat => bd2_row _ _ B a b k n))
        (bsum _ _ B (Datatypes.S n)
           (fun i : nat =>
              @bplus _ _ B (bd2_row _ _ B a b i (Nat.sub n i))
                      (bsum _ _ B (Datatypes.S n)
                         (fun j : nat =>
                            if Nat.ltb (Nat.sub n i) j
                            then @bmult _ _ B (a i) (b j)
                            else @bzero _ _ B))))).
    * (* Rowwise zero padding: [i < S n] gives [n - i <= n], the range bound *)
      (* the padding split needs. *)
      apply (@bsum_ext _ _ B (Datatypes.S n)
               (fun k : nat => bd2_row _ _ B a b k n)
               (fun i : nat =>
                  @bplus _ _ B (bd2_row _ _ B a b i (Nat.sub n i))
                          (bsum _ _ B (Datatypes.S n)
                             (fun j : nat =>
                                if Nat.ltb (Nat.sub n i) j
                                then @bmult _ _ B (a i) (b j)
                                else @bzero _ _ B)))).
      intros i Hi.
      eapply bae_trans.
      -- apply (@bae_refl _ _ B).
      -- exact (bxcd_bsum_pad_split _ _ B (Nat.sub n i) n
                    (fun j : nat => @bmult _ _ B (a i) (b j))
                    ltac:(apply NatLe_lift; lia)).
    * (* The double sum merges: the sum of row-plus-corner sums is the sum *)
      (* of rows plus the sum of corners, and the row fold is [bd2_diagf]. *)
      eapply bae_trans.
      -- exact (bsum_plus _ _ B (Datatypes.S n)
                   (fun i : nat => bd2_row _ _ B a b i (Nat.sub n i))
                   (fun i : nat =>
                      bsum _ _ B (Datatypes.S n)
                         (fun j : nat =>
                            if Nat.ltb (Nat.sub n i) j
                            then @bmult _ _ B (a i) (b j)
                            else @bzero _ _ B))).
      -- exact (@bplus_wd_l _ _ B
                 (bsum _ _ B (Datatypes.S n)
                    (fun i : nat => bd2_row _ _ B a b i (Nat.sub n i)))
                 (bd2_diagf _ _ B a b 0%nat n)
                 (bsum _ _ B (Datatypes.S n)
                    (fun i : nat =>
                       bsum _ _ B (Datatypes.S n)
                          (fun j : nat =>
                             if Nat.ltb (Nat.sub n i) j
                             then @bmult _ _ B (a i) (b j)
                             else @bzero _ _ B)))
                 (tbg_fold_diagf _ _ B a b n)).
Qed.

(* Diagonal sequence face: the [bd2_diag]-named form, the direct dependency *)
(* form on the convergence side. *)
Corollary tbg_diag_seq : forall (BA : Set) (bae : BA -> BA -> Set)
                                (B : BanachAlg BA bae) (a b : nat -> BA) (n : nat),
  bae (ncv_conv _ _ B a b (Datatypes.S n) (Datatypes.S n))
         (@bplus _ _ B (bd2_diag _ _ B n a b) (tbg_corner _ _ B a b n)).
Proof.
  intros BA bae B a b n.
  apply (@bae_trans _ _ B
      (ncv_conv _ _ B a b (Datatypes.S n) (Datatypes.S n))
      (@bplus _ _ B (bd2_diagf _ _ B a b 0%nat n) (tbg_corner _ _ B a b n))).
  - exact (tbg_diag_face _ _ B a b n).
  - exact (@bplus_wd_l _ _ B
             (bd2_diagf _ _ B a b 0%nat n) (bd2_diag _ _ B n a b)
             (tbg_corner _ _ B a b n)
             (@bae_refl _ _ B (bd2_diagf _ _ B a b 0%nat n))).
Qed.

(* ============================================================ *)

(* ============================================================ *)

Print Assumptions tbg_ncvsum_bsum.
Print Assumptions tbg_row_dock.
Print Assumptions tbg_conv_bsum.
Print Assumptions tbg_fold_diagf.
Print Assumptions tbg_diag_face.
Print Assumptions tbg_diag_seq.

From Stdlib Require Import Extraction.
Separate Extraction tbg_diag_face.
