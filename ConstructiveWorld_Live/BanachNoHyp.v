(* ConstructiveWorld-Set — binomial theorem and exponential series re-proven without premise fields. *)

(** * BanachNoHyp: assumption-free re-derivations of the binomial family.

    Mission.  Six statements of [UpReqBanachAdd] carry the scalar-image laws
    as explicit premises; on a bare Banach algebra those laws are class
    fields, so the statements can be re-proven without them.  This file
    re-derives the family assumption-free: the machine shape anchors
    [bnh_hplus_shape] and [bnh_hwd_shape] (each field is definitionally the
    premise shape it replaces), the scalar face, the Pascal pairing pieces,
    the binomial theorem [bnh_bpow_add] (keeping the commutativity premise
    [hab : bae (a*b) (b*a)]), and the exponential-series reassembly
    [bnh_esp_binom].  Eight assumption-free helper lemmas of
    [UpReqBanachAdd] are reused verbatim without re-proof.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp], [UpReqBanachProd], [UpReqBanachAdd] of this
      development.

    References.  This development, ConstructiveWorld-Main BanachNoHyp.v,
      the baseline module whose statement names are carried over here
      verbatim.

    Constructivity.  All statements close with real proofs; the statement
      faces are entirely [Set]-carried ([bae] for equality, [QltT]/[QleT']/
      [sigT] for order and existence); [bae] goals are met through
      definitional [change]s and explicit middle-term chains of [bae_trans];
      [Print Assumptions] closes every statement.  Extraction gives
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" BanachNoHyp.v] compiles
      cleanly (exit 0); the artifact starts with [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachAdd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 0. Machine shape anchors: fields versus explicit premises ================= *)

(* Each anchor is a [Definition] whose type is the old explicit-premise
   shape and whose body is the class field: type checking is the machine
   verification, and the extracted form shows the field use directly. *)

(* Anchor one: the [bcoef_plus] field has exactly the [hplus] shape
   (additivity of the scalar image). *)
Definition bnh_hplus_shape (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q r : Q) :
  bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)) (@bcoef _ _ B (q + r)%Q)
  := @bcoef_plus _ _ B q r.

(* Anchor two: the [bcoef_wd] field has exactly the [hwd] shape (congruence
   of the scalar image under [Qeq]). *)
Definition bnh_hwd_shape (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q r : Q) :
  q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)
  := fun Hqr : q == r => @bcoef_wd _ _ B q r (qeq_imp_qeqT q r Hqr).

(* ================= Section 1. Scalar face, assumption-free ================= *)

(* Scalar pairing merge (counterpart of [bpa_scal_plus] with its [hplus]
   premise discharged): [bcoef q * T + bcoef r * T] equals
   [bcoef (q + r) * T] — symmetry of right distributivity, then the class
   field [bcoef_plus] through the right slot of [bmult_wd]. *)
Lemma bnh_scal_plus : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q r : Q) (T : BA),
  bae (@bplus _ _ B (@bmult _ _ B (@bcoef _ _ B q) T) (@bmult _ _ B (@bcoef _ _ B r) T))
         (@bmult _ _ B (@bcoef _ _ B (q + r)%Q) T).
Proof.
  intros BA bae B q r T. eapply bae_trans.
  - apply (@bae_sym _ _ B).
    exact (@bdistrib_r _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r) T).
  - apply (@bmult_wd _ _ B (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)) T
                       (@bcoef _ _ B (q + r)%Q) T).
    + exact (@bcoef_plus _ _ B q r).
    + apply (@bae_refl _ _ B).
Qed.

(* Congruence under multiplication (counterpart of the [hwd]-carrying core
   step): [q == r] forces [bcoef q * X] and [bcoef r * X] equal, through the
   class field [bcoef_wd]. *)
Lemma bnh_mult_coef_wd : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q r : Q) (X : BA),
  q == r ->
  bae (@bmult _ _ B (@bcoef _ _ B q) X) (@bmult _ _ B (@bcoef _ _ B r) X).
Proof.
  intros BA bae B q r X H.
  apply (@bmult_wd _ _ B (@bcoef _ _ B q) X (@bcoef _ _ B r) X).
  - exact (@bcoef_wd _ _ B q r (qeq_imp_qeqT q r H)).
  - apply (@bae_refl _ _ B).
Qed.

(* ================= Section 2. Pascal pairing pieces, assumption-free ================= *)

(* Pairing middle (counterpart of [bpa_pair_mid]): [gA i + gB (S i)] equals
   [h (S i)] whenever [: i < n'].  The coefficients satisfy
   [: C(n', i) + C(n', S i) = C(S n', S i)] definitionally — the Pascal
   recursion pairs the middle terms; the power of [b] re-indexes since
   [: S(n' - S i) = n' - i]; the merge step uses [bnh_scal_plus], whose
   foundation is the class field [bcoef_plus]. *)
Lemma bnh_pair_mid : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n' i : nat),
  (i < n')%nat ->
  bae (@bplus _ _ B
            (@bmult _ _ B (@bcoef _ _ B (bpa_binom n' i))
                      (@bmult _ _ B (bpow BA bae B a (Datatypes.S i))
                               (bpow BA bae B b (Nat.sub n' i))))
            (@bmult _ _ B (@bcoef _ _ B (bpa_binom n' (Datatypes.S i)))
                      (@bmult _ _ B (bpow BA bae B a (Datatypes.S i))
                               (bpow BA bae B b (Datatypes.S (Nat.sub n' (Datatypes.S i)))))))
         (@bmult _ _ B (@bcoef _ _ B (bpa_binom (Datatypes.S n') (Datatypes.S i)))
                   (@bmult _ _ B (bpow BA bae B a (Datatypes.S i))
                            (bpow BA bae B b (Nat.sub (Datatypes.S n') (Datatypes.S i))))).
Proof.
  intros BA bae B a b n' i Hi.
  assert (E : (Datatypes.S (Nat.sub n' (Datatypes.S i)))%nat = Nat.sub n' i)
    by lia.
  rewrite E.
  change (bpa_binom (Datatypes.S n') (Datatypes.S i))
    with (bpa_binom n' i + bpa_binom n' (Datatypes.S i))%Q.
  change (bpow BA bae B b (Nat.sub (Datatypes.S n') (Datatypes.S i)))
    with (bpow BA bae B b (Nat.sub n' i)).
  eapply bae_trans.
  - exact (bnh_scal_plus _ _ B (bpa_binom n' i) (bpa_binom n' (Datatypes.S i))
             (@bmult _ _ B (bpow BA bae B a (Datatypes.S i)) (bpow BA bae B b (Nat.sub n' i)))).
  - apply (@bae_refl _ _ B).
Qed.

(* Pairing tail (counterpart of [bpa_pair_tail]): [gA n'] equals
   [h (S n')].  The coefficient closes as
   [: C(S n', S n') = C(n', n') + C(n', S n')] with [: C(n', S n') = 0]
   (out of range, [bpa_binom_out]), through the class field [bcoef_wd]; the
   power of [b] normalizes on both sides definitionally. *)
Lemma bnh_pair_tail : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n' : nat),
  bae (@bmult _ _ B (@bcoef _ _ B (bpa_binom n' n'))
                   (@bmult _ _ B (bpow BA bae B a (Datatypes.S n'))
                            (bpow BA bae B b (Nat.sub n' n'))))
         (@bmult _ _ B (@bcoef _ _ B (bpa_binom (Datatypes.S n') (Datatypes.S n')))
                   (@bmult _ _ B (bpow BA bae B a (Datatypes.S n'))
                            (bpow BA bae B b (Nat.sub (Datatypes.S n')
                                               (Datatypes.S n'))))).
Proof.
  intros BA bae B a b n'.
  change (bpa_binom (Datatypes.S n') (Datatypes.S n'))
    with (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q.
  change (bpow BA bae B b (Nat.sub (Datatypes.S n') (Datatypes.S n')))
    with (bpow BA bae B b (Nat.sub n' n')).
  apply (@bae_sym _ _ B).
  apply (@bmult_wd _ _ B
           (@bcoef _ _ B (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q)
           (@bmult _ _ B (bpow BA bae B a (Datatypes.S n')) (bpow BA bae B b (Nat.sub n' n')))
           (@bcoef _ _ B (bpa_binom n' n'))
           (@bmult _ _ B (bpow BA bae B a (Datatypes.S n')) (bpow BA bae B b (Nat.sub n' n')))).
  - apply (@bcoef_wd _ _ B (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q
             (bpa_binom n' n')).
    apply qeq_imp_qeqT.
    rewrite (qeqT_imp_qeq _ _ (bpa_binom_out n' (Datatypes.S n') (Nat.lt_succ_diag_r n'))).
    apply Qplus_0_r.
  - apply (@bae_refl _ _ B).
Qed.

(* ================= Section 3. The binomial theorem ================= *)

(* Binomial identity for powers of a sum: given [: ab = ba], the power
   [bpow (a+b) n] equals the sum of [: C(n,k) * a^k * b^(n-k)] over
   [: k <= n].  The Pascal induction runs as an explicit chain of thirteen
   middle steps, segment-aligned with [UpReqBanachAdd]: the sum engine of
   [UpReqBanachProd], the assumption-free helpers of [UpReqBanachAdd], and
   the pairing pieces of Section 2 (rooted in the class fields). *)
Lemma bnh_bpow_add : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    bae (bpow BA bae B (@bplus _ _ B a b) n)
           (bsum _ _ B (Datatypes.S n)
              (fun k : nat =>
                 @bmult _ _ B (@bcoef _ _ B (bpa_binom n k))
                          (@bmult _ _ B (bpow BA bae B a k)
                                   (bpow BA bae B b (Nat.sub n k))))).
Proof.
  intros BA bae B a b hab n.
  induction n as [| n' IH].
  - (* Base [: n = 0]: [bone] against [bzero + C(0,0) * (bone * bone)]. *)
    change (bpow BA bae B (@bplus _ _ B a b) 0%nat) with (@bone _ _ B).
    change (bsum _ _ B (Datatypes.S 0%nat)
              (fun k : nat => @bmult _ _ B (@bcoef _ _ B (bpa_binom 0%nat k))
                                       (@bmult _ _ B (bpow BA bae B a k)
                                                (bpow BA bae B b (Nat.sub 0%nat k)))))
      with (@bplus _ _ B (@bzero _ _ B)
              (@bmult _ _ B (@bcoef _ _ B (bpa_binom 0%nat 0%nat))
                       (@bmult _ _ B (@bpow BA bae B a 0%nat)
                                (@bpow BA bae B b (Nat.sub 0%nat 0%nat))))).
    assert (E : bpa_binom 0%nat 0%nat = 1%Q) by reflexivity.
    rewrite E.
    change (@bpow BA bae B a 0%nat) with (@bone _ _ B).
    change (@bpow BA bae B b (Nat.sub 0%nat 0%nat)) with (@bone _ _ B).
    assert (HX : bae (@bmult _ _ B (@bcoef _ _ B 1%Q)
                                  (@bmult _ _ B (@bone _ _ B) (@bone _ _ B)))
                        (@bone _ _ B)).
    { eapply bae_trans.
      - apply (@bmult_wd _ _ B (@bcoef _ _ B 1%Q)
                 (@bmult _ _ B (@bone _ _ B) (@bone _ _ B))
                 (@bone _ _ B)
                 (@bmult _ _ B (@bone _ _ B) (@bone _ _ B))).
        + exact (@bcoef_one _ _ B).
        + apply (@bae_refl _ _ B).
      - eapply bae_trans.
        + exact (@bmult_one_l _ _ B (@bmult _ _ B (@bone _ _ B) (@bone _ _ B))).
        + exact (@bmult_one_l _ _ B (@bone _ _ B)). }
    eapply bae_trans.
    + apply (@bae_sym _ _ B). exact (@bplus_zero_l BA bae B (@bone _ _ B)).
    + apply (@bplus_wd_r BA bae B).
      apply (@bae_sym _ _ B). exact HX.
  - (* Induction step: Pascal pairing assembly. *)
    set (g := fun k : nat =>
                @bmult _ _ B (@bcoef _ _ B (bpa_binom n' k))
                         (@bmult _ _ B (bpow BA bae B a k)
                                  (bpow BA bae B b (Nat.sub n' k)))).
    set (gA := fun k : nat =>
                 @bmult _ _ B (@bcoef _ _ B (bpa_binom n' k))
                          (@bmult _ _ B (bpow BA bae B a (Datatypes.S k))
                                   (bpow BA bae B b (Nat.sub n' k)))).
    set (gB := fun k : nat =>
                 @bmult _ _ B (@bcoef _ _ B (bpa_binom n' k))
                          (@bmult _ _ B (bpow BA bae B a k)
                                   (bpow BA bae B b (Datatypes.S (Nat.sub n' k))))).
    set (h := fun k : nat =>
                @bmult _ _ B (@bcoef _ _ B (bpa_binom (Datatypes.S n') k))
                         (@bmult _ _ B (bpow BA bae B a k)
                                  (bpow BA bae B b (Nat.sub (Datatypes.S n') k)))).
    (* Step one: peel the power and substitute the induction premise. *)
    assert (L1 : bae (@bmult _ _ B (bpow BA bae B (@bplus _ _ B a b) n') (@bplus _ _ B a b))
                        (@bmult _ _ B (bsum _ _ B (Datatypes.S n') g)
                                  (@bplus _ _ B a b))).
    { exact (@bmult_wd _ _ B (bpow BA bae B (@bplus _ _ B a b) n')
                       (@bplus _ _ B a b)
                       (bsum _ _ B (Datatypes.S n') g)
                       (@bplus _ _ B a b) IH
                       (@bae_refl _ _ B (@bplus _ _ B a b))). }
    (* Step two: pull the summand factor inside the sum, in the symmetric
       direction of the right-multiplication factoring. *)
    assert (L2 : bae (@bmult _ _ B (bsum _ _ B (Datatypes.S n') g)
                                  (@bplus _ _ B a b))
                        (bsum _ _ B (Datatypes.S n')
                                  (fun k : nat => @bmult _ _ B (g k) (@bplus _ _ B a b)))).
    { apply (@bae_sym _ _ B).
      exact (bpa_bsum_mult_r _ _ B (Datatypes.S n') (@bplus _ _ B a b) g). }
    (* Step three: split each term by left distributivity into its [: a]
       and [: b] parts, sum-wise. *)
    assert (L3 : bae (bsum _ _ B (Datatypes.S n')
                                  (fun k : nat => @bmult _ _ B (g k) (@bplus _ _ B a b)))
                        (@bplus _ _ B (bsum _ _ B (Datatypes.S n')
                                            (fun k : nat => @bmult _ _ B (g k) a))
                                  (bsum _ _ B (Datatypes.S n')
                                            (fun k : nat => @bmult _ _ B (g k) b)))).
    { eapply bae_trans.
      - apply (bsum_ext _ _ B (Datatypes.S n')
                  (fun k : nat => @bmult _ _ B (g k) (@bplus _ _ B a b))
                  (fun k : nat =>
                     @bplus _ _ B (@bmult _ _ B (g k) a) (@bmult _ _ B (g k) b))).
        intros k _. apply (@bdistrib_l _ _ B (g k) a b).
      - apply (bsum_plus _ _ B (Datatypes.S n')
                  (fun k : nat => @bmult _ _ B (g k) a)
                  (fun k : nat => @bmult _ _ B (g k) b)). }
    (* Step four: normalize the [: a] parts by lifting the power, and the
       [: b] parts by commutativity. *)
    assert (L4 : bae (@bplus _ _ B (bsum _ _ B (Datatypes.S n')
                                            (fun k : nat => @bmult _ _ B (g k) a))
                                  (bsum _ _ B (Datatypes.S n')
                                            (fun k : nat => @bmult _ _ B (g k) b)))
                        (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (bsum _ _ B (Datatypes.S n') gB))).
    { apply (@bplus_wd _ _ B
               (bsum _ _ B (Datatypes.S n') (fun k : nat => @bmult _ _ B (g k) a))
               (bsum _ _ B (Datatypes.S n') (fun k : nat => @bmult _ _ B (g k) b))
               (bsum _ _ B (Datatypes.S n') gA)
               (bsum _ _ B (Datatypes.S n') gB)).
      - apply (bsum_ext _ _ B (Datatypes.S n')
                  (fun k : nat => @bmult _ _ B (g k) a) gA).
        intros k _.
        exact (bpa_term_A _ _ B a b hab (bpa_binom n' k) k (Nat.sub n' k)).
      - apply (bsum_ext _ _ B (Datatypes.S n')
                  (fun k : nat => @bmult _ _ B (g k) b) gB).
        intros k _.
        exact (bpa_term_B _ _ B a b (bpa_binom n' k) k (Nat.sub n' k)). }
    (* Step five: re-index the second sum, lifting its leading term. *)
    assert (L5 : bae (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (bsum _ _ B (Datatypes.S n') gB))
                        (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bplus_wd_r BA bae B). exact (bsum_rot _ _ B n' gB). }
    (* Step six: split the tail term off the first sum, closing in the
       definitional sum shape. *)
    assert (L6 : bae (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus _ _ B (@bplus _ _ B (bsum _ _ B n' gA) (gA n'))
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bae_refl _ _ B). }
    (* Step seven: rearrange by commutativity and associativity — the
       leading term of the second sum first, the tail term of the first sum
       last, the two main stretches side by side. *)
    assert (L7 : bae (@bplus _ _ B (@bplus _ _ B (bsum _ _ B n' gA) (gA n'))
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus _ _ B (@bplus _ _ B (gB 0%nat) (bsum _ _ B n' gA))
                                  (@bplus _ _ B (bsum _ _ B n'
                                                (fun i : nat => gB (Datatypes.S i)))
                                            (gA n')))).
    { eapply bae_trans.
      - exact (bplus_swap4 _ _ B (bsum _ _ B n' gA) (gA n') (gB 0%nat)
                   (bsum _ _ B n' (fun i : nat => gB (Datatypes.S i)))).
      - apply (@bplus_wd _ _ B (@bplus _ _ B (bsum _ _ B n' gA) (gB 0%nat))
                 (@bplus _ _ B (gA n')
                            (bsum _ _ B n' (fun i : nat => gB (Datatypes.S i))))
                 (@bplus _ _ B (gB 0%nat) (bsum _ _ B n' gA))
                 (@bplus _ _ B (bsum _ _ B n'
                               (fun i : nat => gB (Datatypes.S i)))
                            (gA n'))).
        + exact (@bplus_comm _ _ B (bsum _ _ B n' gA) (gB 0%nat)).
        + exact (@bplus_comm _ _ B (gA n')
                   (bsum _ _ B n' (fun i : nat => gB (Datatypes.S i)))). }
    assert (L8 : bae (@bplus _ _ B (@bplus _ _ B (gB 0%nat) (bsum _ _ B n' gA))
                                  (@bplus _ _ B (bsum _ _ B n'
                                                (fun i : nat => gB (Datatypes.S i)))
                                            (gA n')))
                        (@bplus _ _ B (gB 0%nat)
                           (@bplus _ _ B (@bplus _ _ B (bsum _ _ B n' gA)
                                                (bsum _ _ B n'
                                                   (fun i : nat => gB (Datatypes.S i))))
                                     (gA n')))).
    { eapply bae_trans.
      - apply (@bae_sym _ _ B).
        exact (@bplus_assoc _ _ B (gB 0%nat) (bsum _ _ B n' gA)
                 (@bplus _ _ B (bsum _ _ B n' (fun i : nat => gB (Datatypes.S i)))
                            (gA n'))).
      - apply (@bplus_wd_r BA bae B).
        exact (@bplus_assoc _ _ B (bsum _ _ B n' gA)
                 (bsum _ _ B n' (fun i : nat => gB (Datatypes.S i)))
                 (gA n')). }
    (* Step eight: merge the Pascal middle — sum the two stretches into one,
       merge pointwise by the pairing piece [bnh_pair_mid], and align the
       head and tail terms. *)
    assert (L9 : bae (@bplus _ _ B (gB 0%nat)
                                  (@bplus _ _ B (@bplus _ _ B (bsum _ _ B n' gA)
                                                       (bsum _ _ B n'
                                                          (fun i : nat => gB (Datatypes.S i))))
                                            (gA n')))
                        (@bplus _ _ B (gB 0%nat)
                                  (@bplus _ _ B (bsum _ _ B n'
                                                (fun i : nat =>
                                                   @bplus _ _ B (gA i)
                                                     (gB (Datatypes.S i))))
                                            (gA n')))).
    { apply (@bplus_wd_r BA bae B
               (@bplus _ _ B (@bplus _ _ B (bsum _ _ B n' gA)
                                  (bsum _ _ B n'
                                     (fun i : nat => gB (Datatypes.S i))))
                          (gA n'))
               (@bplus _ _ B (bsum _ _ B n'
                             (fun i : nat => @bplus _ _ B (gA i) (gB (Datatypes.S i))))
                          (gA n'))
               (gB 0%nat)).
      apply (@bplus_wd_l BA bae B
               (@bplus _ _ B (bsum _ _ B n' gA)
                          (bsum _ _ B n' (fun i : nat => gB (Datatypes.S i))))
               (bsum _ _ B n'
                  (fun i : nat => @bplus _ _ B (gA i) (gB (Datatypes.S i))))
               (gA n')).
      apply (@bae_sym _ _ B).
      exact (bsum_plus _ _ B n' gA (fun i : nat => gB (Datatypes.S i))). }
    assert (L10 : bae (@bplus _ _ B (gB 0%nat)
                                   (@bplus _ _ B (bsum _ _ B n'
                                                 (fun i : nat =>
                                                    @bplus _ _ B (gA i)
                                                      (gB (Datatypes.S i))))
                                              (gA n')))
                         (@bplus _ _ B (gB 0%nat)
                                   (@bplus _ _ B (bsum _ _ B n'
                                                 (fun i : nat => h (Datatypes.S i)))
                                              (gA n')))).
    { apply (@bplus_wd_r BA bae B
               (@bplus _ _ B (bsum _ _ B n'
                             (fun i : nat => @bplus _ _ B (gA i) (gB (Datatypes.S i))))
                          (gA n'))
               (@bplus _ _ B (bsum _ _ B n' (fun i : nat => h (Datatypes.S i)))
                          (gA n'))
               (gB 0%nat)).
      apply (@bplus_wd_l BA bae B
               (bsum _ _ B n'
                  (fun i : nat => @bplus _ _ B (gA i) (gB (Datatypes.S i))))
               (bsum _ _ B n' (fun i : nat => h (Datatypes.S i)))
               (gA n')).
      apply (bsum_ext _ _ B n'
                (fun i : nat => @bplus _ _ B (gA i) (gB (Datatypes.S i)))
                (fun i : nat => h (Datatypes.S i))).
      intros i Hi.
      exact (bnh_pair_mid _ _ B a b n' i Hi). }
    assert (L11 : bae (@bplus _ _ B (gB 0%nat)
                                   (@bplus _ _ B (bsum _ _ B n'
                                                 (fun i : nat => h (Datatypes.S i)))
                                              (gA n')))
                         (@bplus _ _ B (@bplus _ _ B (gB 0%nat)
                                               (bsum _ _ B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (gA n'))).
    { exact (@bplus_assoc _ _ B (gB 0%nat)
               (bsum _ _ B n' (fun i : nat => h (Datatypes.S i))) (gA n')). }
    assert (L12 : bae (@bplus _ _ B (@bplus _ _ B (gB 0%nat)
                                               (bsum _ _ B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (gA n'))
                         (@bplus _ _ B (@bplus _ _ B (h 0%nat)
                                               (bsum _ _ B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (h (Datatypes.S n')))).
    { apply (@bplus_wd _ _ B
               (@bplus _ _ B (gB 0%nat)
                          (bsum _ _ B n' (fun i : nat => h (Datatypes.S i))))
               (gA n')
               (@bplus _ _ B (h 0%nat)
                          (bsum _ _ B n' (fun i : nat => h (Datatypes.S i))))
               (h (Datatypes.S n'))).
      - apply (@bplus_wd _ _ B (gB 0%nat)
                 (bsum _ _ B n' (fun i : nat => h (Datatypes.S i)))
                 (h 0%nat)
                 (bsum _ _ B n' (fun i : nat => h (Datatypes.S i)))).
        + exact (bpa_pair_head _ _ B a b n').
        + apply (@bae_refl _ _ B).
      - exact (bnh_pair_tail _ _ B a b n'). }
    (* Step nine: the target sum closes by the reverse rotation, i.e. the
       definitional sum shape. *)
    assert (L13 : bae (@bplus _ _ B (@bplus _ _ B (h 0%nat)
                                               (bsum _ _ B n'
                                                  (fun i : nat => h (Datatypes.S i))))
                                            (h (Datatypes.S n')))
                         (bsum _ _ B (Datatypes.S (Datatypes.S n')) h)).
    { change (bsum _ _ B (Datatypes.S (Datatypes.S n')) h)
        with (@bplus _ _ B (bsum _ _ B (Datatypes.S n') h) (h (Datatypes.S n'))).
      eapply bae_trans.
      - apply (@bplus_wd_l BA bae B).
        apply (@bae_sym _ _ B). exact (bsum_rot _ _ B n' h).
      - apply (@bae_refl _ _ B). }
    (* Peel the power definitionally and chain the thirteen steps. *)
    change (bpow BA bae B (@bplus _ _ B a b) (Datatypes.S n'))
      with (@bmult _ _ B (bpow BA bae B (@bplus _ _ B a b) n') (@bplus _ _ B a b)).
    exact (@bae_trans _ _ B _ _ _ L1
             (@bae_trans _ _ B _ _ _ L2
                (@bae_trans _ _ B _ _ _ L3
                   (@bae_trans _ _ B _ _ _ L4
                      (@bae_trans _ _ B _ _ _ L5
                         (@bae_trans _ _ B _ _ _ L6
                            (@bae_trans _ _ B _ _ _ L7
                               (@bae_trans _ _ B _ _ _ L8
                                  (@bae_trans _ _ B _ _ _ L9
                                     (@bae_trans _ _ B _ _ _ L10
                                        (@bae_trans _ _ B _ _ _ L11
                                           (@bae_trans _ _ B _ _ _ L12 L13)))))))))))).
Qed.

(* ================= Section 4. Binomial reassembly of the exponential series ================= *)

(* Term level (counterpart of [bpa_esp_term_binom], commutativity premise
   kept): [bpow (a+b) k * (1/k!)] equals the sum of
   [: (C(k,j)/k!) * a^j * b^(k-j)] over [: j <= k] — the binomial theorem
   through the left slot of [bmult_wd], the scalar factored out of the sum,
   and the coefficients repacked through the class fields. *)
Lemma bnh_esp_term_binom : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall k : nat,
    bae (@bmult _ _ B (bpow BA bae B (@bplus _ _ B a b) k)
                     (@bcoef _ _ B (/ q_fact k)))
           (bsum _ _ B (Datatypes.S k)
              (fun j : nat =>
                 @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                          (@bmult _ _ B (bpow BA bae B a j)
                                   (bpow BA bae B b (Nat.sub k j))))).
Proof.
  intros BA bae B a b hab k.
  set (F := fun j : nat =>
              @bmult _ _ B (@bcoef _ _ B (bpa_binom k j))
                       (@bmult _ _ B (bpow BA bae B a j)
                                (bpow BA bae B b (Nat.sub k j)))).
  eapply bae_trans.
  - apply (@bmult_wd _ _ B (bpow BA bae B (@bplus _ _ B a b) k)
                     (@bcoef _ _ B (/ q_fact k))
                     (bsum _ _ B (Datatypes.S k) F)
                     (@bcoef _ _ B (/ q_fact k))).
    + exact (bnh_bpow_add _ _ B a b hab k).
    + apply (@bae_refl _ _ B).
  - eapply bae_trans.
    + apply (@bae_sym _ _ B).
      exact (bsum_scal _ _ B (Datatypes.S k) (/ q_fact k) F).
    + apply (bsum_ext _ _ B (Datatypes.S k)
                (fun j : nat => @bmult _ _ B (F j) (@bcoef _ _ B (/ q_fact k)))
                (fun j : nat =>
                   @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                            (@bmult _ _ B (bpow BA bae B a j)
                                     (bpow BA bae B b (Nat.sub k j))))).
      intros j _.
      exact (bpa_scal_repack _ _ B (bpa_binom k j) (/ q_fact k)
               (@bmult _ _ B (bpow BA bae B a j) (bpow BA bae B b (Nat.sub k j)))).
Qed.

(* Series level (counterpart of [bpa_esp_binom]): the exponential partial
   sum of [: a + b] equals the double sum of
   [: (C(k,j)/k!) * a^j * b^(k-j)] — read as a sum, then term-wise by the
   previous statement. *)
Lemma bnh_esp_binom : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall n : nat,
    bae (exp_series_partial BA bae B (@bplus _ _ B a b) n)
           (bsum _ _ B (Datatypes.S n)
              (fun k : nat =>
                 bsum _ _ B (Datatypes.S k)
                   (fun j : nat =>
                      @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                               (@bmult _ _ B (bpow BA bae B a j)
                                        (bpow BA bae B b (Nat.sub k j)))))).
Proof.
  intros BA bae B a b hab n.
  eapply bae_trans.
  - exact (esp_as_bsum _ _ B (@bplus _ _ B a b) n).
  - apply (bsum_ext _ _ B (Datatypes.S n)
              (fun k : nat => @bmult _ _ B (bpow BA bae B (@bplus _ _ B a b) k)
                                      (@bcoef _ _ B (/ q_fact k)))
              (fun k : nat =>
                 bsum _ _ B (Datatypes.S k)
                   (fun j : nat =>
                      @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                               (@bmult _ _ B (bpow BA bae B a j)
                                        (bpow BA bae B b (Nat.sub k j)))))).
    intros k _.
    exact (bnh_esp_term_binom _ _ B a b hab k).
Qed.

(* Closing notes.  The six premise-carrying statements of
   [UpReqBanachAdd] are re-derived here without them; downstream consumers
   requiring the assumption-free forms use this file's [bnh_] family, while
   the existing [bpa_] family remains in place unchanged — the two coexist
   and do not replace one another.  The premise [hab : bae (a*b) (b*a)] is
   the mathematical commutativity premise of the non-commutative binomial
   theorem, kept in place as in the [bpa_] family; it is a mathematical
   premise, not an interface assumption. *)

Print Assumptions bnh_hplus_shape.
Print Assumptions bnh_hwd_shape.
Print Assumptions bnh_scal_plus.
Print Assumptions bnh_mult_coef_wd.
Print Assumptions bnh_pair_mid.
Print Assumptions bnh_pair_tail.
Print Assumptions bnh_bpow_add.
Print Assumptions bnh_esp_term_binom.
Print Assumptions bnh_esp_binom.
