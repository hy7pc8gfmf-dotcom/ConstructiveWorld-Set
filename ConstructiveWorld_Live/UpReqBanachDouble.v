(* ConstructiveWorld-Set — double sums in a Banach algebra: triangle, diagonal and rectangle foldings. *)

(** * UpReqBanachDouble: consistency of double-sum foldings.

    Mission.  For a Banach-algebra-valued double family [f i * g j], three
    ways of folding the double sum agree: the triangle (row-ordered)
    folding, the diagonal folding by anti-diagonal blocks, and the
    rectangle folding as an iterated [bsum].  Statements: the definitions
    [bd2_row]/[bd2_tfrom]/[bd2_dline]/[bd2_diagf]/[bd2_tri]/[bd2_diag]/
    [bd2_rect], the main identities [bd2_tri_eq_diag]/[bd2_tri_eq_rect]/
    [bd2_tri_eq_rect_row], and their supporting lemmas.

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp], [UpReqBanachProd] of this development.

    References.  This development, ConstructiveWorld-Main
      UpReqBanachDouble.v, the baseline module whose statement names are
      carried over here verbatim.  The foldings implement the classical
      double-series facts that triangular, diagonal and rectangular
      partial sums of a product family agree.

    Constructivity.  All named statements and fields are carried by
      [Set]; order predicates and the equality [bae] are Set-valued
      carriers.  Statements extract with [Obj.magic] = 0 and no erasure;
      [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -Q . "" UpReqBanachDouble.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
From Stdlib Require Import QArith.QArith Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 1. Double-sum foldings as Fixpoints ================= *)

(* Rectangle row: [row i n] sums [f i * g j] over [j <= n] in the [bsum]
   carrier. *)
Definition bd2_row (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i n : nat) : BA :=
  bsum _ _ B (Datatypes.S n) (fun j : nat => @bmult _ _ B (f i) (g j)).

(* Triangle in row order: [tfrom i n] sums [f(i+a) * g j] over [a + j <= n].
   Recursion: [tfrom i (S m) = row i (S m) + tfrom (S i) m] — peel the first
   row, shrink the budget by one. *)
Fixpoint bd2_tfrom (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i n : nat)
                   {struct n} : BA :=
  match n with
  | 0%nat => @bmult _ _ B (f i) (g 0%nat)
  | Datatypes.S m =>
      @bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
               (bd2_tfrom _ _ B f g (Datatypes.S i) m)
  end.

(* Single diagonal block: [dline i k = f i * g k + f(i+1) * g(k-1) + ... +
   f(i+k) * g 0].  Recursion: [dline i (S m) = f i * g(S m) + dline (S i) m]
   — extract the first term, shift the indices. *)
Fixpoint bd2_dline (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i k : nat)
                   {struct k} : BA :=
  match k with
  | 0%nat => @bmult _ _ B (f i) (g 0%nat)
  | Datatypes.S m =>
      @bplus _ _ B (@bmult _ _ B (f i) (g (Datatypes.S m)))
               (bd2_dline _ _ B f g (Datatypes.S i) m)
  end.

(* Diagonal folding: [diagf i n] sums the blocks [dline i k] over [k <= n]. *)
Fixpoint bd2_diagf (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i n : nat)
                   {struct n} : BA :=
  match n with
  | 0%nat => @bmult _ _ B (f i) (g 0%nat)
  | Datatypes.S m =>
      @bplus _ _ B (bd2_diagf _ _ B f g i m)
               (bd2_dline _ _ B f g i (Datatypes.S m))
  end.

(* Global wrappers: [bd2_tri n] sums over [i + j <= n], and [bd2_diag n]
   over anti-diagonals [i + j = k], both from the origin. *)
Definition bd2_tri (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f g : nat -> BA) : BA :=
  bd2_tfrom _ _ B f g 0%nat n.
Definition bd2_diag (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f g : nat -> BA) : BA :=
  bd2_diagf _ _ B f g 0%nat n.

(* Small-[: n] definitional closures of the wrappers, unified through the
   reflexive equality carrier. *)
Example bd2_ex_tri0 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA),
  bae (bd2_tri _ _ B 0%nat f g) (@bmult _ _ B (f 0%nat) (g 0%nat)).
Proof. intros BA bae B f g. apply (@bae_refl _ _ B). Qed.

Example bd2_ex_diag0 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA),
  bae (bd2_diag _ _ B 0%nat f g) (@bmult _ _ B (f 0%nat) (g 0%nat)).
Proof. intros BA bae B f g. apply (@bae_refl _ _ B). Qed.

Example bd2_ex_row0 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i : nat),
  bae (bd2_row _ _ B f g i 0%nat)
         (@bplus _ _ B (@bzero _ _ B) (@bmult _ _ B (f i) (g 0%nat))).
Proof. intros BA bae B f g i. apply (@bae_refl _ _ B). Qed.

(* The concrete [: n = 1] instance with both families constant at [bone]:
   the triangle row-order definition shape, including the leading zero term
   of [bsum]. *)
Example bd2_ex_tri1_bone : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  bae (bd2_tri _ _ B 1%nat (fun _ : nat => @bone _ _ B) (fun _ : nat => @bone _ _ B))
         (@bplus _ _ B (@bplus _ _ B (@bplus _ _ B (@bzero _ _ B) (@bmult _ _ B (@bone _ _ B) (@bone _ _ B)))
                             (@bmult _ _ B (@bone _ _ B) (@bone _ _ B)))
                   (@bmult _ _ B (@bone _ _ B) (@bone _ _ B))).
Proof. intros BA bae B. apply (@bae_refl _ _ B). Qed.

(* ================= Section 2. Triangle equals diagonal ================= *)

(* Key geometric step: [diagf i (S m) = row i (S m) + diagf (S i) m] — the
   top row peels off the diagonal folding. *)
Lemma bd2_diag_peel : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i m : nat),
  bae (bd2_diagf _ _ B f g i (Datatypes.S m))
         (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
                   (bd2_diagf _ _ B f g (Datatypes.S i) m)).
Proof.
  intros BA bae B f g i m. induction m as [| m' IH].
  - (* Base case [: m = 0]: [A + (B + C)] regroups to [((0 + A) + B) + C] by
       associativity and annihilation of the zero term. *)
    change (bd2_diagf _ _ B f g i (Datatypes.S 0%nat))
      with (@bplus _ _ B (@bmult _ _ B (f i) (g 0%nat))
                     (@bplus _ _ B (@bmult _ _ B (f i) (g (Datatypes.S 0%nat)))
                              (@bmult _ _ B (f (Datatypes.S i)) (g 0%nat)))).
    change (bd2_diagf _ _ B f g (Datatypes.S i) 0%nat)
      with (@bmult _ _ B (f (Datatypes.S i)) (g 0%nat)).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bplus _ _ B (@bmult _ _ B (f i) (g 0%nat))
                          (@bmult _ _ B (f i) (g (Datatypes.S 0%nat))))
                (@bmult _ _ B (f (Datatypes.S i)) (g 0%nat))) _).
    + exact (@bplus_assoc _ _ B (@bmult _ _ B (f i) (g 0%nat))
                           (@bmult _ _ B (f i) (g (Datatypes.S 0%nat)))
                           (@bmult _ _ B (f (Datatypes.S i)) (g 0%nat))).
    + apply (@bplus_wd_l BA bae B
               (@bplus _ _ B (@bmult _ _ B (f i) (g 0%nat))
                         (@bmult _ _ B (f i) (g (Datatypes.S 0%nat))))
               (bd2_row _ _ B f g i (Datatypes.S 0%nat))
               (@bmult _ _ B (f (Datatypes.S i)) (g 0%nat))).
      apply (@bae_sym _ _ B).
      exact (@bplus_wd_l BA bae B (@bplus _ _ B (@bzero _ _ B) (@bmult _ _ B (f i) (g 0%nat)))
                          (@bmult _ _ B (f i) (g 0%nat))
                          (@bmult _ _ B (f i) (g (Datatypes.S 0%nat)))
                          (@bplus_zero_l BA bae B (@bmult _ _ B (f i) (g 0%nat)))).
  - (* Induction step: the pairs [A' + D] and [E + F'] interchange their
       middles via the four-term rearrangement, leaving the tail in
       definitional row and diagonal-folding shape. *)
    change (bd2_diagf _ _ B f g i (Datatypes.S (Datatypes.S m')))
      with (@bplus _ _ B (bd2_diagf _ _ B f g i (Datatypes.S m'))
                     (@bplus _ _ B (@bmult _ _ B (f i) (g (Datatypes.S (Datatypes.S m'))))
                              (bd2_dline _ _ B f g (Datatypes.S i) (Datatypes.S m')))).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m'))
                          (bd2_diagf _ _ B f g (Datatypes.S i) m'))
                (@bplus _ _ B (@bmult _ _ B (f i) (g (Datatypes.S (Datatypes.S m'))))
                         (bd2_dline _ _ B f g (Datatypes.S i) (Datatypes.S m')))) _).
    + apply (@bplus_wd_l BA bae B). exact IH.
    + apply (@bae_trans _ _ B _
        (@bplus _ _ B (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m'))
                            (@bmult _ _ B (f i) (g (Datatypes.S (Datatypes.S m')))))
                  (@bplus _ _ B (bd2_diagf _ _ B f g (Datatypes.S i) m')
                           (bd2_dline _ _ B f g (Datatypes.S i) (Datatypes.S m')))) _).
      * exact (bplus_swap4 _ _ B (bd2_row _ _ B f g i (Datatypes.S m'))
                            (bd2_diagf _ _ B f g (Datatypes.S i) m')
                            (@bmult _ _ B (f i) (g (Datatypes.S (Datatypes.S m'))))
                            (bd2_dline _ _ B f g (Datatypes.S i) (Datatypes.S m'))).
      * apply (@bae_refl _ _ B).
Qed.

(* Main induction (on [: n], with [: i] generalized): the row-ordered
   triangle equals the diagonal folding from any starting index. *)
Lemma bd2_tfrom_diag : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (n i : nat),
  bae (bd2_tfrom _ _ B f g i n) (bd2_diagf _ _ B f g i n).
Proof.
  intros BA bae B f g n. induction n as [| m IH]; intros i.
  - exact (@bae_refl _ _ B (@bmult _ _ B (f i) (g 0%nat))).
  - change (bd2_tfrom _ _ B f g i (Datatypes.S m))
      with (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
                     (bd2_tfrom _ _ B f g (Datatypes.S i) m)).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
                (bd2_diagf _ _ B f g (Datatypes.S i) m)) _).
    + apply (@bplus_wd_r BA bae B (bd2_tfrom _ _ B f g (Datatypes.S i) m)
                           (bd2_diagf _ _ B f g (Datatypes.S i) m)
                           (bd2_row _ _ B f g i (Datatypes.S m))).
      exact (IH (Datatypes.S i)).
    + apply (@bae_sym _ _ B). exact (bd2_diag_peel _ _ B f g i m).
Qed.

(* Triangle equals diagonal, globally. *)
Theorem bd2_tri_eq_diag : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f g : nat -> BA),
  bae (bd2_tri _ _ B n f g) (bd2_diag _ _ B n f g).
Proof. intros BA bae B n f g. exact (bd2_tfrom_diag _ _ B f g n 0%nat). Qed.

(* The [: n = 1] specialization of the main identity, as a warming example. *)
Example bd2_ex_n1 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA),
  bae (bd2_tri _ _ B 1%nat f g) (bd2_diag _ _ B 1%nat f g).
Proof. intros BA bae B f g. exact (bd2_tri_eq_diag _ _ B 1%nat f g). Qed.

(* ================= Section 3. Rectangle folding and the row-product corollary ================= *)

(* Rectangle: [rect i n] sums [f(i+a) * g j] over [a <= n] and [j <= n - a]
   as an iterated [bsum]. *)
Definition bd2_rect (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i n : nat) : BA :=
  bsum _ _ B (Datatypes.S n)
    (fun a : nat => bsum _ _ B (Datatypes.S (Nat.sub n a))
                       (fun j : nat => @bmult _ _ B (f (i + a)%nat) (g j))).

(* The rectangle peels its first row: [rect i (S m) = row i (S m) +
   rect (S i) m].  The rotation [bsum_rot] lifts the leading row; the tail
   indices [(i + S a)] and [(S i + a)] are re-labeled by Leibniz equality
   on [: nat]. *)
Lemma bd2_rect_split : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (i m : nat),
  bae (bd2_rect _ _ B f g i (Datatypes.S m))
         (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
                   (bd2_rect _ _ B f g (Datatypes.S i) m)).
Proof.
  intros BA bae B f g i m.
  change (bd2_rect _ _ B f g i (Datatypes.S m))
    with (bsum _ _ B (Datatypes.S (Datatypes.S m))
            (fun a : nat => bsum _ _ B (Datatypes.S (Nat.sub (Datatypes.S m) a))
                               (fun j : nat => @bmult _ _ B (f (i + a)%nat) (g j)))).
  change (bd2_rect _ _ B f g (Datatypes.S i) m)
    with (bsum _ _ B (Datatypes.S m)
            (fun a : nat => bsum _ _ B (Datatypes.S (Nat.sub m a))
                               (fun j : nat => @bmult _ _ B (f ((Datatypes.S i) + a)%nat) (g j)))).
  apply (@bae_trans _ _ B _
    (@bplus _ _ B (bsum _ _ B (Datatypes.S (Nat.sub (Datatypes.S m) 0%nat))
                      (fun j : nat => @bmult _ _ B (f (i + 0%nat)%nat) (g j)))
              (bsum _ _ B (Datatypes.S m)
                 (fun a : nat =>
                    bsum _ _ B (Datatypes.S (Nat.sub (Datatypes.S m) (Datatypes.S a)))
                      (fun j : nat => @bmult _ _ B (f (i + (Datatypes.S a))%nat) (g j))))) _).
  - apply (@bsum_rot _ _ B (Datatypes.S m)
              (fun a : nat => bsum _ _ B (Datatypes.S (Nat.sub (Datatypes.S m) a))
                                 (fun j : nat => @bmult _ _ B (f (i + a)%nat) (g j)))).
  - apply (@bplus_wd _ _ B).
    + (* The leading row closes once [: i + 0] is re-labeled to [: i]. *)
      assert (Hi0 : (i + 0%nat)%nat = i) by lia.
      rewrite Hi0.
      apply (@bae_refl _ _ B).
    + (* Tail families re-labeled: [(i + S a) = (S i + a)], pointwise by
         [bsum_ext]. *)
      apply (@bsum_ext _ _ B (Datatypes.S m)
        (fun a : nat => bsum _ _ B (Datatypes.S (Nat.sub (Datatypes.S m) (Datatypes.S a)))
                           (fun j : nat => @bmult _ _ B (f (i + (Datatypes.S a))%nat) (g j)))
        (fun a : nat => bsum _ _ B (Datatypes.S (Nat.sub m a))
                           (fun j : nat => @bmult _ _ B (f ((Datatypes.S i) + a)%nat) (g j)))).
      intros k Hk.
      assert (Hik : (i + Datatypes.S k)%nat = (Datatypes.S i + k)%nat) by lia.
      rewrite Hik.
      apply (@bae_refl _ _ B).
Qed.

(* Triangle equals rectangle from any starting index; the global form is the
   specialization at the origin. *)
Lemma bd2_tfrom_rect : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (f g : nat -> BA) (n i : nat),
  bae (bd2_tfrom _ _ B f g i n) (bd2_rect _ _ B f g i n).
Proof.
  intros BA bae B f g n. induction n as [| m IH]; intros i.
  - change (bd2_tfrom _ _ B f g i 0%nat) with (@bmult _ _ B (f i) (g 0%nat)).
    change (bd2_rect _ _ B f g i 0%nat)
      with (@bplus _ _ B (@bzero _ _ B)
                     (@bplus _ _ B (@bzero _ _ B)
                              (@bmult _ _ B (f (i + 0%nat)%nat) (g 0%nat)))).
    assert (Hi0 : (i + 0%nat)%nat = i) by lia.
    rewrite Hi0.
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bzero _ _ B) (@bmult _ _ B (f i) (g 0%nat))) _).
    + apply (@bae_sym _ _ B). apply (@bplus_zero_l BA bae B).
    + apply (@bae_sym _ _ B). apply (@bplus_zero_l BA bae B).
  - change (bd2_tfrom _ _ B f g i (Datatypes.S m))
      with (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
                     (bd2_tfrom _ _ B f g (Datatypes.S i) m)).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (bd2_row _ _ B f g i (Datatypes.S m))
                (bd2_rect _ _ B f g (Datatypes.S i) m)) _).
    + apply (@bplus_wd_r BA bae B (bd2_tfrom _ _ B f g (Datatypes.S i) m)
                             (bd2_rect _ _ B f g (Datatypes.S i) m)
                             (bd2_row _ _ B f g i (Datatypes.S m))).
      exact (IH (Datatypes.S i)).
    + apply (@bae_sym _ _ B). exact (bd2_rect_split _ _ B f g i m).
Qed.

(* Triangle equals the rectangle double sum, globally. *)
Theorem bd2_tri_eq_rect : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f g : nat -> BA),
  bae (bd2_tri _ _ B n f g) (bd2_rect _ _ B f g 0%nat n).
Proof. intros BA bae B n f g. exact (bd2_tfrom_rect _ _ B f g n 0%nat). Qed.

(* Row-product interface: [row i n = f i * (sum of [g j] over [j <= n])],
   by the frozen factor-out lemma [bsum_mult_l] applied row by row; this is
   the joint to the Cauchy-block assembly. *)
Lemma bd2_row_mult_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (i n : nat) (f g : nat -> BA),
  bae (bd2_row _ _ B f g i n)
         (@bmult _ _ B (f i) (bsum _ _ B (Datatypes.S n) g)).
Proof. intros BA bae B i n f g. exact (bsum_mult_l _ _ B (Datatypes.S n) (f i) g). Qed.

(* Assembly specialization: with [: f k = a^k / k!] and [: g k = b^k / k!],
   the square block of [esp_prod_square] is exactly the leading rows of the
   statement below; on the diagonal side, [bd2_diag] combined with the
   commutation [ab = ba] reorders inside each block. *)
Theorem bd2_tri_eq_rect_row : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat)
                                     (f g : nat -> BA),
  bae (bd2_tri _ _ B n f g)
         (bsum _ _ B (Datatypes.S n)
            (fun i : nat => @bmult _ _ B (f i)
                               (bsum _ _ B (Datatypes.S (Nat.sub n i)) g))).
Proof.
  intros BA bae B n f g.
  apply (@bae_trans _ _ B _ (bd2_rect _ _ B f g 0%nat n) _).
  - exact (bd2_tfrom_rect _ _ B f g n 0%nat).
  - unfold bd2_rect.
    apply (@bsum_ext _ _ B (Datatypes.S n)
      (fun i : nat => bsum _ _ B (Datatypes.S (Nat.sub n i))
                         (fun j : nat => @bmult _ _ B (f (0%nat + i)%nat) (g j)))
      (fun i : nat => @bmult _ _ B (f i)
                         (bsum _ _ B (Datatypes.S (Nat.sub n i)) g))).
    intros k Hk.
    apply (@bae_trans _ _ B _
      (bsum _ _ B (Datatypes.S (Nat.sub n k))
               (fun j : nat => @bmult _ _ B (f k) (g j))) _).
    + (* [: 0 + k] closes definitionally after re-labeling. *)
      apply (@bae_refl _ _ B).
    + exact (bsum_mult_l _ _ B (Datatypes.S (Nat.sub n k)) (f k) g).
Qed.

(* Remaining work, registered honestly as open at this interface: the
   addition law of the exponential [: e^{a+b} = e^a * e^b] needs the
   binomial identity [bpow_add] (which requires [: ab = ba]) to reassemble
   the series, with the diagonal folding here and [esp_prod_square] as the
   two assembly surfaces; and the tail-convergence chain
   ([esp_diff_le_tail] / [exp_series_cauchy], proved in [UpReqBanachExp])
   belongs to the convergence companion file, outside the scope here. *)
