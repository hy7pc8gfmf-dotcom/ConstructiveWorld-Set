(** * UpReqBanachProd: algebraic laws for finite sums and the Cauchy
      product of exponential partial sums.

    Mission.  Finite sums in a Banach algebra ([bsum], [bsum_ext],
 [bsum_plus], [bsum_scal], [bsum_mult_l]), the four-term AC
 rearrangement [bplus_swap4], commutation of powers [bpow_comm_r],
 the partial-sum presentation of the exponential series
 [esp_as_bsum], and the product rearrangements [bsum_prod] /
 [esp_prod_square] for the Cauchy product of two partial sums.

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [Lia].
 Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
 [UpReqBanachExp] of this development.

    References.  This development, UpReqBanachProd.v, the baseline
 module in ConstructiveWorld-Main whose statement names are carried
 over here verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements are carried by [Set]
 (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id], [NatLe]);
 statements extract with [Obj.magic] = 0 and no erasure; [coqchk]
 reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachProd.v]
 compiles cleanly (exit 0); the first eight bytes of the artifact
 are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Section 1. Partial sums in the Banach algebra: [bsum n f] sums     *)
(*   [f 0, ..., f (n-1)]; [bsum (S m) f = bsum m f + f m].             *)
(* ============================================================ *)

Fixpoint bsum (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f : nat -> BA) : BA :=
  match n with
  | 0%nat => @bzero _ _ B
  | Datatypes.S m => @bplus _ _ B (bsum _ _ B m f) (f m)
  end.

(* ============================================================ *)
(* Section 2. Summation engine at the carrier-equality level.         *)
(* ============================================================ *)

(* Left multiplication pulls out of a sum: [sum (c * g i) = c * sum g]
   (left distributivity; no commutativity of multiplication needed). *)
Lemma bsum_mult_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (c : BA)
                            (g : nat -> BA),
  bae (bsum _ _ B n (fun i : nat => @bmult _ _ B c (g i)))
         (@bmult _ _ B c (bsum _ _ B n g)).
Proof.
  intros BA bae B n c g. induction n as [| m IH].
  - (* Base case: [bsum 0 = bzero] and [c * bzero = bzero]. *)
    apply (@bae_sym _ _ B). exact (@bmult_zero _ _ B c).
  - change (bsum _ _ B (Datatypes.S m) (fun i : nat => @bmult _ _ B c (g i)))
      with (@bplus _ _ B (bsum _ _ B m (fun i : nat => @bmult _ _ B c (g i)))
                     (@bmult _ _ B c (g m))).
    eapply bae_trans.
    + (* The induction case replaces the first summand:
         [X + c*(g m) -> (c * sum_m g) + c*(g m)]. *)
      apply (@bplus_wd_l BA bae B). exact IH.
    + (* [c * (sum_m g + g m)] redistributes back (the definitional
         change absorbs the [bsum (S m) g] shape). *)
      apply (@bae_sym _ _ B). exact (@bdistrib_l _ _ B c (bsum _ _ B m g) (g m)).
Qed.

(* Pointwise carrier equality of summands gives equality of sums. *)
Lemma bsum_ext : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f g : nat -> BA),
  (forall k : nat, (k < n)%nat -> bae (f k) (g k)) ->
  bae (bsum _ _ B n f) (bsum _ _ B n g).
Proof.
  intros BA bae B n f g. induction n as [| m IH]; intros H.
  - apply (@bae_refl _ _ B).
  - change (bsum _ _ B (Datatypes.S m) f) with (@bplus _ _ B (bsum _ _ B m f) (f m)).
    change (bsum _ _ B (Datatypes.S m) g) with (@bplus _ _ B (bsum _ _ B m g) (g m)).
    apply (@bplus_wd _ _ B).
    + apply IH. intros k Hk. apply H. lia.
    + apply H. lia.
Qed.

(* Four-term AC rearrangement: [(a+b)+(c+d) = (a+c)+(b+d)]. *)
Lemma bplus_swap4 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b c d : BA),
  bae (@bplus _ _ B (@bplus _ _ B a b) (@bplus _ _ B c d))
         (@bplus _ _ B (@bplus _ _ B a c) (@bplus _ _ B b d)).
Proof.
  intros BA bae B a b c d.
  apply (@bae_trans _ _ B _ _ _
    (@bae_sym _ _ B _ _ (@bplus_assoc _ _ B a b (@bplus _ _ B c d)))
    (@bae_trans _ _ B _ _ _
      (@bplus_wd_r BA bae B (@bplus _ _ B b (@bplus _ _ B c d))
                     (@bplus _ _ B (@bplus _ _ B b c) d) a
        (@bplus_assoc _ _ B b c d))
      (@bae_trans _ _ B _ _ _
        (@bplus_wd_r BA bae B (@bplus _ _ B (@bplus _ _ B b c) d)
                       (@bplus _ _ B (@bplus _ _ B c b) d) a
          (@bplus_wd_l BA bae B (@bplus _ _ B b c) (@bplus _ _ B c b) d
             (@bplus_comm _ _ B b c)))
        (@bae_trans _ _ B _ _ _
          (@bplus_wd_r BA bae B (@bplus _ _ B (@bplus _ _ B c b) d)
                         (@bplus _ _ B c (@bplus _ _ B b d)) a
            (@bae_sym _ _ B _ _ (@bplus_assoc _ _ B c b d)))
          (@bplus_assoc _ _ B a c (@bplus _ _ B b d)))))).
Qed.

(* Additivity of the sum: [sum (f+g) = sum f + sum g]. *)
Lemma bsum_plus : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f g : nat -> BA),
  bae (bsum _ _ B n (fun k : nat => @bplus _ _ B (f k) (g k)))
         (@bplus _ _ B (bsum _ _ B n f) (bsum _ _ B n g)).
Proof.
  intros BA bae B n f g. induction n as [| m IH].
  - apply (@bae_sym _ _ B). apply (@bplus_zero_l BA bae B).
  - change (bsum _ _ B (Datatypes.S m) (fun k : nat => @bplus _ _ B (f k) (g k)))
      with (@bplus _ _ B (bsum _ _ B m (fun k : nat => @bplus _ _ B (f k) (g k)))
                     (@bplus _ _ B (f m) (g m))).
    change (@bplus _ _ B (bsum _ _ B (Datatypes.S m) f) (bsum _ _ B (Datatypes.S m) g))
      with (@bplus _ _ B (@bplus _ _ B (bsum _ _ B m f) (f m))
                     (@bplus _ _ B (bsum _ _ B m g) (g m))).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bplus _ _ B (bsum _ _ B m f) (bsum _ _ B m g))
                (@bplus _ _ B (f m) (g m))) _).
    + apply (@bplus_wd_l BA bae B). exact IH.
    + exact (bplus_swap4 _ _ B (bsum _ _ B m f) (bsum _ _ B m g) (f m) (g m)).
Qed.

(* Right scalar extraction: [sum (f k * bcoef c) = (sum f) * bcoef c]
   (right distributivity). *)
Lemma bsum_scal : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (c : Q) (f : nat -> BA),
  bae (bsum _ _ B n (fun k : nat => @bmult _ _ B (f k) (@bcoef _ _ B c)))
         (@bmult _ _ B (bsum _ _ B n f) (@bcoef _ _ B c)).
Proof.
  intros BA bae B n c f. induction n as [| m IH].
  - (* Base case: both sides are [bzero]; [bcoef c * bzero = bzero]
     via scalar centrality and right annihilation. *)
    apply (@bae_sym _ _ B).
    apply (@bae_trans _ _ B _ (@bmult _ _ B (@bcoef _ _ B c) (@bzero _ _ B)) _).
    + exact (@bcoef_comm _ _ B c (@bzero _ _ B)).
    + exact (@bmult_zero _ _ B (@bcoef _ _ B c)).
  - change (bsum _ _ B (Datatypes.S m)
              (fun k : nat => @bmult _ _ B (f k) (@bcoef _ _ B c)))
      with (@bplus _ _ B (bsum _ _ B m (fun k : nat => @bmult _ _ B (f k) (@bcoef _ _ B c)))
                     (@bmult _ _ B (f m) (@bcoef _ _ B c))).
    eapply bae_trans.
    + apply (@bplus_wd_l BA bae B). exact IH.
    + apply (@bae_sym _ _ B).
      exact (@bdistrib_r _ _ B (bsum _ _ B m f) (f m) (@bcoef _ _ B c)).
Qed.

(* ============================================================ *)
(* Section 3. Commutation engine: if [a*b = b*a] then [a^n * b = b * a^n]
   for every [n] (the key step when commuting a power past [b]). *)
(* ============================================================ *)

Lemma bpow_comm_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    bae (@bmult _ _ B (bpow BA bae B a n) b) (@bmult _ _ B b (bpow BA bae B a n)).
Proof.
  intros BA bae B a b hab n. induction n as [| m IH].
  - (* Base case: [bone * b = b * bone = b]. *)
    apply (@bae_trans _ _ B _ b _).
    + exact (@bmult_one_l _ _ B b).
    + apply (@bae_sym _ _ B). exact (@bmult_one_r _ _ B b).
  - change (bpow BA bae B a (Datatypes.S m)) with (@bmult _ _ B (bpow BA bae B a m) a).
    (* Five-step chain: ((a^m)*a)*b = (a^m)*(a*b) = (a^m)*(b*a)
              = ((a^m)*b)*a = (b*(a^m))*a = b*((a^m)*a). *)
    apply (@bae_trans _ _ B _ (@bmult _ _ B (bpow BA bae B a m) (@bmult _ _ B a b)) _).
    + apply (@bae_sym _ _ B). exact (@bmult_assoc _ _ B (bpow BA bae B a m) a b).
    + apply (@bae_trans _ _ B _ (@bmult _ _ B (bpow BA bae B a m) (@bmult _ _ B b a)) _).
      * apply (@bmult_wd _ _ B (bpow BA bae B a m) (@bmult _ _ B a b)
                           (bpow BA bae B a m) (@bmult _ _ B b a)).
        -- apply (@bae_refl _ _ B).
        -- exact hab.
      * apply (@bae_trans _ _ B _
                 (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a m) b) a) _).
        -- exact (@bmult_assoc _ _ B (bpow BA bae B a m) b a).
        -- apply (@bae_trans _ _ B _
                     (@bmult _ _ B b (@bmult _ _ B (bpow BA bae B a m) a)) _).
           ++ apply (@bae_trans _ _ B _
                        (@bmult _ _ B (@bmult _ _ B b (bpow BA bae B a m)) a) _).
           ** apply (@bmult_wd _ _ B (@bmult _ _ B (bpow BA bae B a m) b) a
                                 (@bmult _ _ B b (bpow BA bae B a m)) a IH).
              apply (@bae_refl _ _ B).
           ** apply (@bae_sym _ _ B).
              exact (@bmult_assoc _ _ B b (bpow BA bae B a m) a).
           ++ (* [b * ((a^m)*a) = b * (bpow a (S m))] holds by the
                 definitional shape, hence reflexivity. *)
              apply (@bae_refl _ _ B).
Qed.

(* ============================================================ *)
(* Section 4. The exponential partial sum as a finite sum:
   [exp_series_partial a n = sum_{k<=n} (a^k)/k!]. *)
(* ============================================================ *)

Lemma esp_as_bsum : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (n : nat),
  bae (exp_series_partial BA bae B a n)
         (bsum _ _ B (Datatypes.S n)
            (fun k : nat => @bmult _ _ B (bpow BA bae B a k)
                                    (@bcoef _ _ B (/ q_fact k)))).
Proof.
  intros BA bae B a n. induction n as [| m IH].
  - (* Base case: [bone = bzero + bone * bcoef 1] (since [q_fact 0 = 1]). *)
    assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
    change (exp_series_partial BA bae B a 0%nat) with (@bone _ _ B).
    change (bsum _ _ B (Datatypes.S 0%nat)
              (fun k : nat => @bmult _ _ B (bpow BA bae B a k)
                                      (@bcoef _ _ B (/ q_fact k))))
      with (@bplus _ _ B (@bzero _ _ B)
              (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B (/ q_fact 0%nat)))).
    rewrite Hq0.
    apply (@bae_sym _ _ B).
    eapply bae_trans.
    + apply (@bplus_wd_r BA bae B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B 1%Q)) (@bone _ _ B)).
      eapply bae_trans.
      * exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)).
      * exact (@bcoef_one _ _ B).
    + exact (@bplus_zero_l BA bae B (@bone _ _ B)).
  - change (exp_series_partial BA bae B a (Datatypes.S m))
      with (@bplus _ _ B (exp_series_partial BA bae B a m)
               (@bmult _ _ B (bpow BA bae B a (Datatypes.S m))
                         (@bcoef _ _ B (/ q_fact (Datatypes.S m))))).
    change (bsum _ _ B (Datatypes.S (Datatypes.S m))
              (fun k : nat => @bmult _ _ B (bpow BA bae B a k)
                                      (@bcoef _ _ B (/ q_fact k))))
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S m)
                        (fun k : nat => @bmult _ _ B (bpow BA bae B a k)
                                                (@bcoef _ _ B (/ q_fact k))))
                     (@bmult _ _ B (bpow BA bae B a (Datatypes.S m))
                               (@bcoef _ _ B (/ q_fact (Datatypes.S m))))).
    apply (@bplus_wd _ _ B).
    + exact IH.
    + apply (@bae_refl _ _ B).
Qed.

(* ============================================================ *)
(* Section 5. The Cauchy product of partial sums: the square identity. *)
(* ============================================================ *)

(* Product of two sums as a double (square) sum:
   [(sum_{j<=m} f j) * (sum_{i<=n} g i) = sum_{j<=m} sum_{i<=n} f j * g i].
   Only right distributivity and associativity are used; the order of
   the factors [f j * g i] never changes. *)
Lemma bsum_prod : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (m n : nat)
                         (f g : nat -> BA),
  bae (@bmult _ _ B (bsum _ _ B (Datatypes.S m) f) (bsum _ _ B (Datatypes.S n) g))
         (bsum _ _ B (Datatypes.S m)
            (fun j : nat => bsum _ _ B (Datatypes.S n)
               (fun i : nat => @bmult _ _ B (f j) (g i)))).
Proof.
  intros BA bae B m n f g. induction m as [| m' IH].
  - (* Base case m=0: annihilate [bzero] on both sides, then pull
     [f 0] out of the inner sum. *)
    change (bsum _ _ B (Datatypes.S 0%nat) f)
      with (@bplus _ _ B (@bzero _ _ B) (f 0%nat)).
    change (bsum _ _ B (Datatypes.S 0%nat)
              (fun j : nat => bsum _ _ B (Datatypes.S n)
                 (fun i : nat => @bmult _ _ B (f j) (g i))))
      with (@bplus _ _ B (@bzero _ _ B)
              (bsum _ _ B (Datatypes.S n)
                 (fun i : nat => @bmult _ _ B (f 0%nat) (g i)))).
    apply (@bae_trans _ _ B _
      (@bmult _ _ B (f 0%nat) (bsum _ _ B (Datatypes.S n) g)) _).
    + apply (@bmult_wd _ _ B (@bplus _ _ B (@bzero _ _ B) (f 0%nat))
                         (bsum _ _ B (Datatypes.S n) g) (f 0%nat)
                         (bsum _ _ B (Datatypes.S n) g)).
      * exact (bplus_zero_l BA bae B (f 0%nat)).
      * apply (@bae_refl _ _ B).
    + (* [f 0 * sum g = bzero + W] where [W = sum (f 0 * g i)]. *)
      apply (@bae_sym _ _ B).
      apply (@bae_trans _ _ B
        (@bplus _ _ B (@bzero _ _ B)
           (bsum _ _ B (Datatypes.S n)
              (fun i : nat => @bmult _ _ B (f 0%nat) (g i))))
        (bsum _ _ B (Datatypes.S n)
           (fun i : nat => @bmult _ _ B (f 0%nat) (g i)))
        (@bmult _ _ B (f 0%nat) (bsum _ _ B (Datatypes.S n) g))).
      * apply (@bplus_zero_l BA bae B).
      * exact (bsum_mult_l _ _ B (Datatypes.S n) (f 0%nat) g).
  - (* Induction step: right distributivity splits off the [S m'] term,
     then the induction case and left extraction. *)
    apply (@bae_trans _ _ B
      (@bmult _ _ B (bsum _ _ B (Datatypes.S (Datatypes.S m')) f)
                (bsum _ _ B (Datatypes.S n) g))
      (@bplus _ _ B (@bmult _ _ B (bsum _ _ B (Datatypes.S m') f)
                          (bsum _ _ B (Datatypes.S n) g))
                (@bmult _ _ B (f (Datatypes.S m'))
                         (bsum _ _ B (Datatypes.S n) g)))
      (bsum _ _ B (Datatypes.S (Datatypes.S m'))
         (fun j : nat => bsum _ _ B (Datatypes.S n)
            (fun i : nat => @bmult _ _ B (f j) (g i))))).
    + exact (@bdistrib_r _ _ B (bsum _ _ B (Datatypes.S m') f)
                          (f (Datatypes.S m'))
                          (bsum _ _ B (Datatypes.S n) g)).
    + apply (@bplus_wd _ _ B).
      * exact IH.
      * apply (@bae_sym _ _ B).
        exact (bsum_mult_l _ _ B (Datatypes.S n) (f (Datatypes.S m')) g).
Qed.

(* Main statement: [esp n a * esp n b = sum_{j<=n} sum_{i<=n}
   (a^j/j!) * (b^i/i!)] — the square of the partial sums is the double
   sum of the termwise products (via [esp_as_bsum] twice and
   [bsum_prod]). *)
Lemma esp_prod_square : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n : nat),
  bae (@bmult _ _ B (exp_series_partial BA bae B a n)
                   (exp_series_partial BA bae B b n))
         (bsum _ _ B (Datatypes.S n)
            (fun j : nat => bsum _ _ B (Datatypes.S n)
               (fun i : nat =>
                  @bmult _ _ B (@bmult _ _ B (bpow BA bae B a j)
                                    (@bcoef _ _ B (/ q_fact j)))
                           (@bmult _ _ B (bpow BA bae B b i)
                                    (@bcoef _ _ B (/ q_fact i)))))).
Proof.
  intros BA bae B a b n.
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (bsum _ _ B (Datatypes.S n)
                 (fun k : nat => @bmult _ _ B (bpow BA bae B a k)
                                         (@bcoef _ _ B (/ q_fact k))))
              (bsum _ _ B (Datatypes.S n)
                 (fun k : nat => @bmult _ _ B (bpow BA bae B b k)
                                         (@bcoef _ _ B (/ q_fact k))))) _).
  - apply (@bmult_wd _ _ B).
    + exact (esp_as_bsum _ _ B a n).
    + exact (esp_as_bsum _ _ B b n).
  - exact (bsum_prod _ _ B n n
             (fun k : nat => @bmult _ _ B (bpow BA bae B a k) (@bcoef _ _ B (/ q_fact k)))
             (fun k : nat => @bmult _ _ B (bpow BA bae B b k) (@bcoef _ _ B (/ q_fact k)))).
Qed.

(* ============================================================ *)
(* Section 6. Three reindexing lemmas for finite sums (rotation and
   two predecessor shifts), the combinatorial preparation for the
   binomial expansion of the exponential of a sum. *)
(* ============================================================ *)

(* Rotation: [sum_{k<=n} f k = f 0 + sum_{k<=n-1} f (S k)] (the first
   term is pulled out). *)
Lemma bsum_rot : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f : nat -> BA),
  bae (bsum _ _ B (Datatypes.S n) f)
         (@bplus _ _ B (f 0%nat)
                     (bsum _ _ B n (fun k : nat => f (Datatypes.S k)))).
Proof.
  intros BA bae B n f. induction n as [| m IH].
  - change (bsum _ _ B (Datatypes.S 0%nat) f)
      with (@bplus _ _ B (@bzero _ _ B) (f 0%nat)).
    change (bsum _ _ B 0%nat (fun k : nat => f (Datatypes.S k)))
      with (@bzero _ _ B).
    apply (@bplus_comm _ _ B (@bzero _ _ B) (f 0%nat)).
  - change (bsum _ _ B (Datatypes.S (Datatypes.S m)) f)
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S m) f) (f (Datatypes.S m))).
    change (@bplus _ _ B (f 0%nat)
              (bsum _ _ B (Datatypes.S m) (fun k : nat => f (Datatypes.S k))))
      with (@bplus _ _ B (f 0%nat)
              (@bplus _ _ B (bsum _ _ B m (fun k : nat => f (Datatypes.S k)))
                       (f (Datatypes.S m)))).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bplus _ _ B (f 0%nat)
                          (bsum _ _ B m (fun k : nat => f (Datatypes.S k))))
                (f (Datatypes.S m))) _).
    + apply (@bplus_wd_l BA bae B). exact IH.
    + apply (@bae_sym _ _ B).
      apply (@bplus_assoc _ _ B (f 0%nat)
               (bsum _ _ B m (fun k : nat => f (Datatypes.S k)))
               (f (Datatypes.S m))).
Qed.

(* Predecessor shift: [sum_{j<=n+1} f (j-1) = f 0 + sum_{k<=n} f k]. *)
Lemma bsum_shift_pred : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f : nat -> BA),
  bae (bsum _ _ B (Datatypes.S (Datatypes.S n))
              (fun j : nat => f (Nat.sub j 1)))
         (@bplus _ _ B (f 0%nat) (bsum _ _ B (Datatypes.S n) f)).
Proof.
  intros BA bae B n f.
  (* Set G := fun j => f (j-1); [G 0 = f 0] and [G (S k) = f k] hold
     definitionally. *)
  set (G := fun j : nat => f (Nat.sub j 1)).
  induction n as [| m IH].
  - change (bsum _ _ B (Datatypes.S (Datatypes.S 0%nat)) G)
      with (@bplus _ _ B (@bplus _ _ B (@bzero _ _ B) (f 0%nat)) (f 0%nat)).
    change (bsum _ _ B (Datatypes.S 0%nat) f)
      with (@bplus _ _ B (@bzero _ _ B) (f 0%nat)).
    (* [(0+X)+X = X+(0+X)], through the intermediate [X+X]. *)
    apply (@bae_trans _ _ B _ (@bplus _ _ B (f 0%nat) (f 0%nat)) _).
    + eapply bae_trans.
      * apply (@bae_sym _ _ B).
        exact (@bplus_assoc _ _ B (@bzero _ _ B) (f 0%nat) (f 0%nat)).
      * exact (bplus_zero_l BA bae B (@bplus _ _ B (f 0%nat) (f 0%nat))).
    + apply (@bplus_wd_r BA bae B (f 0%nat) (@bplus _ _ B (@bzero _ _ B) (f 0%nat))).
      apply (@bae_sym _ _ B). exact (bplus_zero_l BA bae B (f 0%nat)).
  - change (bsum _ _ B (Datatypes.S (Datatypes.S (Datatypes.S m))) G)
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S (Datatypes.S m)) G)
                     (G (Datatypes.S (Datatypes.S m)))).
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bplus _ _ B (f 0%nat) (bsum _ _ B (Datatypes.S m) f))
                (G (Datatypes.S (Datatypes.S m)))) _).
    + apply (@bplus_wd_l BA bae B). exact IH.
    + (* After reassociation (symmetry) the last term [G (S (S m)) =
         f (S (S m) - 1) = f (S m)] closes definitionally. *)
      apply (@bae_sym _ _ B).
      apply (@bplus_assoc _ _ B (f 0%nat) (bsum _ _ B (Datatypes.S m) f)
               (G (Datatypes.S (Datatypes.S m)))).
Qed.

(* Predecessor shift, original order:
   [sum_{k<=n} f k + f 0 = sum_{j<=n+1} f (j-1)]. *)
Lemma bsum_shift_pred2 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (f : nat -> BA),
  bae (@bplus _ _ B (bsum _ _ B (Datatypes.S n) f) (f 0%nat))
         (bsum _ _ B (Datatypes.S (Datatypes.S n))
            (fun j : nat => f (Nat.sub j 1))).
Proof.
  intros BA bae B n f.
  apply (@bae_trans _ _ B _
    (@bplus _ _ B (f 0%nat) (bsum _ _ B (Datatypes.S n) f)) _).
  - apply (@bplus_comm _ _ B (bsum _ _ B (Datatypes.S n) f) (f 0%nat)).
  - apply (@bae_sym _ _ B). exact (bsum_shift_pred _ _ B n f).
Qed.

(* ============================================================ *)
(* Scope note (open extensions, no statements are admitted here):      *)
(*   the binomial identity [bpow (a+b) n = sum C(n,k) a^k b^(n-k)]     *)
(*   under [a*b = b*a] (Pascal coefficient layer plus the reindexing   *)
(*   lemmas of Section 6 and the commutation engine of Section 3), and *)
(*   the transposed Cauchy product leading to [exp (a+b)] = exp a*exp b, *)
(*   are future work.  The tail estimates [esp_diff_le_tail] and the   *)
(*   Cauchy property [exp_series_cauchy] of UpReqBanachExp close the   *)
(*   convergence side. *)
(* ============================================================ *)

(* Assumption audit: every named statement must print as closed. *)
Print Assumptions bplus_swap4.
