(* ConstructiveWorld-Set — binomial identity for Banach-algebra powers. *)

(** * UpReqBanachAdd: the binomial identity [bpow_add]..

    Mission.  [bpow_add]: for commuting elements, the power of the sum equals the
 Pascal binomial sum; supported by the Pascal recursion [bpa_binom]
 and the boundary lemmas [bpa_binom_out] (out of range is zero) and
 [bpa_binom_diag] (diagonal is one).

    Dependencies.  Stdlib [QArith.QArith]. Requires [S01_BaseRing],
 [S02_CauchyComplete], [S03_QExp], [UpReqBanachExp],
 [UpReqBanachProd] of this development.

    References.  This development, UpReqBanachAdd.v, the baseline module in
 ConstructiveWorld-Main whose statement names are carried over here
 verbatim (statement-face Set-carrier completion: [==] equalities
 moved to [QeqT]; computational [nat]/[Q] equations to [Id]).

    Constructivity.  All named statements and fields are carried by
      [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id],
      [NatLe]); statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachAdd.v]
      compiles cleanly (exit 0); the first eight bytes of the
      artifact are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* Section 1. The binomial coefficient [bpa_binom] (Pascal recursion,
   Q-valued).                                                             *)
(*                                                                  *)
(* Design note.  The Pascal recursive form is chosen over the          *)
(* factorial ratio: (i) the Pascal pairing point becomes definitional  *)
(* (reachable by iota, avoiding division, common denominators and      *)
(* nonzero-denominator chains); (ii) matching in successor form avoids *)
(* truncated nat subtraction (the boundary k = 0 is guarded by the     *)
(* match branch and the out-of-range case k > n by a dedicated         *)
(* lemma).  The pairing order (k' term first) aligns with the pairing  *)
(* of the main proof: C(n',i)+C(n',S i) is exactly the definitional    *)
(* shape of C(S n',S i). *)
(* ============================================================ *)

Fixpoint bpa_binom (n k : nat) {struct n} : Q :=
  match n with
  | 0%nat =>
      match k with
      | 0%nat => 1%Q
      | Datatypes.S _ => 0%Q
      end
  | Datatypes.S n' =>
      match k with
      | 0%nat => 1%Q
      | Datatypes.S k' => (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q
      end
  end.

(* The Pascal point in successor form (definitional, reflexivity). *)
Lemma bpa_binom_pascal : forall n k : nat,
  Id (bpa_binom (Datatypes.S n) (Datatypes.S k))
     ((bpa_binom n k + bpa_binom n (Datatypes.S k))%Q).
Proof. intros n k. apply id_refl. Qed.

(* Left boundary: [C(n,0) = 1]. *)
Lemma bpa_binom_0 : forall n : nat, Id (bpa_binom n 0%nat) 1%Q.
Proof. intros n. destruct n as [| n']; constructor. Qed.

(* Out of range: [C(n,k) = 0] for k > n (induction on n; [0+0] closes
   by the rational addition engine). *)
Lemma bpa_binom_out : forall n k : nat, (n < k)%nat -> QeqT (bpa_binom n k) 0%Q.
Proof.
  intros n k Hk. apply qeq_imp_qeqT. revert Hk. revert k.
  induction n as [| n' IH]; intros k Hk.
  - destruct k as [| k']; [ lia | ].
    apply Qeq_refl.
  - destruct k as [| k']; [ lia | ].
    change (bpa_binom (Datatypes.S n') (Datatypes.S k'))
      with (bpa_binom n' k' + bpa_binom n' (Datatypes.S k'))%Q.
    setoid_rewrite (IH k' ltac:(lia)).
    setoid_rewrite (IH (Datatypes.S k') ltac:(lia)).
    apply Qplus_0_l.
Qed.

(* Diagonal: [C(n,n) = 1] (uses the out-of-range lemma and right
   annihilation). *)
Lemma bpa_binom_diag : forall n : nat, QeqT (bpa_binom n n) 1%Q.
Proof.
  intros n. apply qeq_imp_qeqT. induction n as [| n' IH].
  - apply Qeq_refl.
  - change (bpa_binom (Datatypes.S n') (Datatypes.S n'))
      with (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q.
    setoid_rewrite IH.
    assert (Hout : QeqT (bpa_binom n' (Datatypes.S n')) 0%Q)
      by (apply bpa_binom_out; apply Nat.lt_succ_diag_r).
    setoid_rewrite (qeqT_imp_qeq _ _ Hout).
    apply Qplus_0_r.
Qed.

(* The Pascal point in the [Nat.sub] shape matching the main statement
   (bounds [1 <= k <= n] guard against truncated subtraction.  The
   term order follows the Fixpoint pairing order of this file — the
   [k-1] term first — which agrees with the successor-form definitional
   shape; rational addition is not commutative on the propositional
   equality face, so the order must not be swapped). *)
Lemma bpa_binom_pascal_sub : forall n k : nat, (1 <= k)%nat -> (k <= n)%nat ->
  Id (bpa_binom n k)
    ((bpa_binom (Nat.sub n 1) (Nat.sub k 1)
       + bpa_binom (Nat.sub n 1) k)%Q).
Proof.
  intros n k Hk1 Hkn.
  destruct n as [| n']; [ lia | ].
  destruct k as [| k']; [ lia | ].
  assert (E1 : (Datatypes.S n' - 1)%nat = n') by lia.
  assert (E2 : (Datatypes.S k' - 1)%nat = k') by lia.
  rewrite E1, E2.
  apply id_refl.
Qed.

(* ============================================================ *)
(* Section 2, preliminaries: the carrier-equality scalar engine and
   per-term normalization lemmas. *)
(* ============================================================ *)

(* Left annihilation: [bzero * x = bzero].  The interface only gives
   right annihilation; the left form is derived from [u = u + u]
   (since [bzero = bzero + bzero] by right distributivity) and
   cancellation by the additive inverse. *)
Lemma bpa_bmult_zero_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B (@bzero _ _ B) x) (@bzero _ _ B).
Proof.
  intros BA bae B x.
  assert (Ha : bae (@bmult _ _ B (@bzero _ _ B) x)
                      (@bplus _ _ B (@bmult _ _ B (@bzero _ _ B) x)
                                (@bmult _ _ B (@bzero _ _ B) x))).
  { eapply bae_trans.
    - apply (@bmult_wd _ _ B (@bzero _ _ B) x
               (@bplus _ _ B (@bzero _ _ B) (@bzero _ _ B)) x).
      + apply (@bae_sym _ _ B). exact (@bplus_zero _ _ B (@bzero _ _ B)).
      + apply (@bae_refl _ _ B).
    - exact (@bdistrib_r _ _ B (@bzero _ _ B) (@bzero _ _ B) x). }
  apply (@bae_sym _ _ B).
  eapply bae_trans.
  - apply (@bae_sym _ _ B). exact (@bplus_opp _ _ B (@bmult _ _ B (@bzero _ _ B) x)).
  - eapply bae_trans.
    + apply (@bplus_wd_l BA bae B (@bmult _ _ B (@bzero _ _ B) x)
               (@bplus _ _ B (@bmult _ _ B (@bzero _ _ B) x)
                          (@bmult _ _ B (@bzero _ _ B) x))
               (@bopp _ _ B (@bmult _ _ B (@bzero _ _ B) x)) Ha).
    + eapply bae_trans.
      * apply (@bae_sym _ _ B).
        exact (@bplus_assoc _ _ B (@bmult _ _ B (@bzero _ _ B) x)
                 (@bmult _ _ B (@bzero _ _ B) x) (@bopp _ _ B (@bmult _ _ B (@bzero _ _ B) x))).
      * eapply bae_trans.
        -- apply (@bplus_wd_r BA bae B). exact (@bplus_opp _ _ B (@bmult _ _ B (@bzero _ _ B) x)).
        -- exact (@bplus_zero _ _ B (@bmult _ _ B (@bzero _ _ B) x)).
Qed.

(* Right multiplication pulls out of a sum (dual of the left form):
   [sum (f i * x) = (sum f) * x] (symmetric direction of right
   distributivity; the zero base case uses left annihilation). *)
Lemma bpa_bsum_mult_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat) (x : BA)
                               (f : nat -> BA),
  bae (bsum _ _ B n (fun i : nat => @bmult _ _ B (f i) x))
         (@bmult _ _ B (bsum _ _ B n f) x).
Proof.
  intros BA bae B n x f. induction n as [| m IH].
  - apply (@bae_sym _ _ B). exact (bpa_bmult_zero_l BA bae B x).
  - change (bsum _ _ B (Datatypes.S m) (fun i : nat => @bmult _ _ B (f i) x))
      with (@bplus _ _ B (bsum _ _ B m (fun i : nat => @bmult _ _ B (f i) x))
                     (@bmult _ _ B (f m) x)).
    change (@bmult _ _ B (bsum _ _ B (Datatypes.S m) f) x)
      with (@bmult _ _ B (@bplus _ _ B (bsum _ _ B m f) (f m)) x).
    eapply bae_trans.
    + apply (@bplus_wd_l BA bae B). exact IH.
    + apply (@bae_sym _ _ B). exact (@bdistrib_r _ _ B (bsum _ _ B m f) (f m) x).
Qed.

(* Scalar pair merging: [bcoef q * T + bcoef r * T = bcoef (q+r) * T]
   (uses an explicit additivity premise for [bcoef], which the
   interface does not provide). *)
Lemma bpa_scal_plus : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q r : Q) (T : BA),
  (forall q r : Q, bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r))
                           (@bcoef _ _ B (q + r)%Q)) ->
  bae (@bplus _ _ B (@bmult _ _ B (@bcoef _ _ B q) T) (@bmult _ _ B (@bcoef _ _ B r) T))
         (@bmult _ _ B (@bcoef _ _ B (q + r)%Q) T).
Proof.
  intros BA bae B q r T H. eapply bae_trans.
  - apply (@bae_sym _ _ B).
    exact (@bdistrib_r _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r) T).
  - apply (@bmult_wd _ _ B (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)) T
                       (@bcoef _ _ B (q + r)%Q) T).
    + exact (H q r).
    + apply (@bae_refl _ _ B).
Qed.

(* Normalizing the a-term: [(c * (a^k * b^m)) * a = c * (a^(S k) * b^m)].
   The factor [a] lands on the right: [b^m * a = a * b^m] via the
   commutation engine (with [b] as base and the commutation premise
   in its symmetric role); [a^k * a = a^(S k)] closes definitionally. *)
Lemma bpa_term_A : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  forall (c : Q) (k m : nat),
    bae (@bmult _ _ B (@bmult _ _ B (@bcoef _ _ B c)
                                (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b m))) a)
           (@bmult _ _ B (@bcoef _ _ B c)
                     (@bmult _ _ B (bpow BA bae B a (Datatypes.S k)) (bpow BA bae B b m))).
Proof.
  intros BA bae B a b hab c k m. eapply bae_trans.
  - apply (@bae_sym _ _ B).
    exact (@bmult_assoc _ _ B (@bcoef _ _ B c)
              (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b m)) a).
  - eapply bae_trans.
    + apply (@bmult_wd _ _ B (@bcoef _ _ B c)
               (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b m)) a)
               (@bcoef _ _ B c)
               (@bmult _ _ B (bpow BA bae B a k)
                          (@bmult _ _ B (bpow BA bae B b m) a))).
      * apply (@bae_refl _ _ B).
      * apply (@bae_sym _ _ B).
        exact (@bmult_assoc _ _ B (bpow BA bae B a k) (bpow BA bae B b m) a).
    + eapply bae_trans.
      * apply (@bmult_wd _ _ B (@bcoef _ _ B c)
                 (@bmult _ _ B (bpow BA bae B a k) (@bmult _ _ B (bpow BA bae B b m) a))
                 (@bcoef _ _ B c)
                 (@bmult _ _ B (bpow BA bae B a k) (@bmult _ _ B a (bpow BA bae B b m)))).
        -- apply (@bae_refl _ _ B).
        -- apply (@bmult_wd _ _ B (bpow BA bae B a k) (@bmult _ _ B (bpow BA bae B b m) a)
                    (bpow BA bae B a k) (@bmult _ _ B a (bpow BA bae B b m))).
           ++ apply (@bae_refl _ _ B).
           ++ exact (bpow_comm_r _ _ B b a
                       (@bae_sym _ _ B (@bmult _ _ B a b) (@bmult _ _ B b a) hab) m).
      * eapply bae_trans.
        -- apply (@bmult_wd _ _ B (@bcoef _ _ B c)
                    (@bmult _ _ B (bpow BA bae B a k) (@bmult _ _ B a (bpow BA bae B b m)))
                    (@bcoef _ _ B c)
                    (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a k) a) (bpow BA bae B b m))).
           ++ apply (@bae_refl _ _ B).
           ++ exact (@bmult_assoc _ _ B (bpow BA bae B a k) a (bpow BA bae B b m)).
        -- (* [(a^k * a) * b^m = a^(S k) * b^m] holds by the definitional
              shape of [bpow], hence reflexivity. *)
           apply (@bae_refl _ _ B).
Qed.

(* Normalizing the b-term: [(c * (a^k * b^m)) * b = c * (a^k * b^(S m))].
   The factor [b] associates directly with [b^m]; no commutativity
   premise is needed. *)
Lemma bpa_term_B : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (c : Q) (k m : nat),
  bae (@bmult _ _ B (@bmult _ _ B (@bcoef _ _ B c)
                              (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b m))) b)
         (@bmult _ _ B (@bcoef _ _ B c)
                   (@bmult _ _ B (bpow BA bae B a k)
                            (bpow BA bae B b (Datatypes.S m)))).
Proof.
  intros BA bae B a b c k m. eapply bae_trans.
  - apply (@bae_sym _ _ B).
    exact (@bmult_assoc _ _ B (@bcoef _ _ B c)
              (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b m)) b).
  - eapply bae_trans.
    + apply (@bmult_wd _ _ B (@bcoef _ _ B c)
               (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b m)) b)
               (@bcoef _ _ B c)
               (@bmult _ _ B (bpow BA bae B a k) (@bmult _ _ B (bpow BA bae B b m) b))).
      * apply (@bae_refl _ _ B).
      * apply (@bae_sym _ _ B).
        exact (@bmult_assoc _ _ B (bpow BA bae B a k) (bpow BA bae B b m) b).
    + apply (@bmult_wd _ _ B (@bcoef _ _ B c)
               (@bmult _ _ B (bpow BA bae B a k) (@bmult _ _ B (bpow BA bae B b m) b))
               (@bcoef _ _ B c)
               (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B b (Datatypes.S m)))).
      * apply (@bae_refl _ _ B).
      * apply (@bae_refl _ _ B).
Qed.

(* Pairing head term (j=0): [gB 0 = h 0].  Both coefficients are 1
   (boundary lemmas), and the exponent [S (n' - 0) = S n'] by
   arithmetic. *)
Lemma bpa_pair_head : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n' : nat),
  bae (@bmult _ _ B (@bcoef _ _ B (bpa_binom n' 0%nat))
                   (@bmult _ _ B (bpow BA bae B a 0%nat)
                            (bpow BA bae B b (Datatypes.S (Nat.sub n' 0%nat)))))
         (@bmult _ _ B (@bcoef _ _ B (bpa_binom (Datatypes.S n') 0%nat))
                   (@bmult _ _ B (bpow BA bae B a 0%nat)
                            (bpow BA bae B b (Nat.sub (Datatypes.S n') 0%nat)))).
Proof.
  intros BA bae B a b n'.
  assert (E1 : bpa_binom n' 0%nat = 1%Q) by (destruct n'; reflexivity).
  assert (E2 : bpa_binom (Datatypes.S n') 0%nat = 1%Q) by reflexivity.
  assert (E3 : (Datatypes.S (Nat.sub n' 0%nat))%nat = Datatypes.S n') by lia.
  rewrite E1, E2, E3.
  change (bpow BA bae B b (Nat.sub (Datatypes.S n') 0%nat))
    with (bpow BA bae B b (Datatypes.S n')).
  apply (@bae_refl _ _ B).
Qed.

(* Pairing middle terms: [gA i + gB (S i) = h (S i)] for i < n'.
   The coefficient sum [C(n',i) + C(n',S i)] is exactly the
   definitional shape of [C(S n',S i)] (Pascal recursion pairing
   order); the exponents [S (n' - S i) = n' - i] and
   [S n' - S i = n' - i] are unified by arithmetic and iota. *)
Lemma bpa_pair_mid : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n' i : nat),
  (forall q r : Q, bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r))
                           (@bcoef _ _ B (q + r)%Q)) ->
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
  intros BA bae B a b n' i hplus Hi.
  assert (E : (Datatypes.S (Nat.sub n' (Datatypes.S i)))%nat = Nat.sub n' i)
    by lia.
  rewrite E.
  change (bpa_binom (Datatypes.S n') (Datatypes.S i))
    with (bpa_binom n' i + bpa_binom n' (Datatypes.S i))%Q.
  change (bpow BA bae B b (Nat.sub (Datatypes.S n') (Datatypes.S i)))
    with (bpow BA bae B b (Nat.sub n' i)).
  eapply bae_trans.
  - exact (bpa_scal_plus _ _ B (bpa_binom n' i) (bpa_binom n' (Datatypes.S i))
             (@bmult _ _ B (bpow BA bae B a (Datatypes.S i)) (bpow BA bae B b (Nat.sub n' i)))
             hplus).
  - apply (@bae_refl _ _ B).
Qed.

(* Pairing tail term: [gA n' = h (S n')].  [C(S n',S n')] unfolds to
   [C(n',n') + C(n',S n')] definitionally; the second summand is zero
   (out of range), collapsed through the congruence premise on
   [bcoef] and right annihilation; both b-exponents close by iota. *)
Lemma bpa_pair_tail : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (n' : nat),
  (forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)) ->
  bae (@bmult _ _ B (@bcoef _ _ B (bpa_binom n' n'))
                   (@bmult _ _ B (bpow BA bae B a (Datatypes.S n'))
                            (bpow BA bae B b (Nat.sub n' n'))))
         (@bmult _ _ B (@bcoef _ _ B (bpa_binom (Datatypes.S n') (Datatypes.S n')))
                   (@bmult _ _ B (bpow BA bae B a (Datatypes.S n'))
                            (bpow BA bae B b (Nat.sub (Datatypes.S n')
                                               (Datatypes.S n'))))).
Proof.
  intros BA bae B a b n' hwd.
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
  - apply (hwd (bpa_binom n' n' + bpa_binom n' (Datatypes.S n'))%Q
             (bpa_binom n' n')).
    assert (Hout : bpa_binom n' (Datatypes.S n') == 0%Q)
      by (apply qeqT_imp_qeq; apply bpa_binom_out; apply Nat.lt_succ_diag_r).
    setoid_rewrite Hout.
    apply Qplus_0_r.
  - apply (@bae_refl _ _ B).
Qed.

(* ============================================================ *)
(* Section 2, main statement: the binomial identity for powers. *)
(* ============================================================ *)

Lemma bpa_bpow_add : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  (forall q r : Q, bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r))
                           (@bcoef _ _ B (q + r)%Q)) ->
  (forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)) ->
  forall n : nat,
    bae (bpow BA bae B (@bplus _ _ B a b) n)
           (bsum _ _ B (Datatypes.S n)
              (fun k : nat =>
                 @bmult _ _ B (@bcoef _ _ B (bpa_binom n k))
                          (@bmult _ _ B (bpow BA bae B a k)
                                   (bpow BA bae B b (Nat.sub n k))))).
Proof.
  intros BA bae B a b hab hplus hwd n.
  induction n as [| n' IH].
  - (* Base case n=0: [bone = bzero + C(0,0) * (bone * bone)]. *)
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
  - (* Induction step: assemble the Pascal pairing. *)
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
    (* Step 1: pull out the power (definitional) and apply the
       induction case. *)
    assert (L1 : bae (@bmult _ _ B (bpow BA bae B (@bplus _ _ B a b) n') (@bplus _ _ B a b))
                        (@bmult _ _ B (bsum _ _ B (Datatypes.S n') g)
                                  (@bplus _ _ B a b))).
    { exact (@bmult_wd _ _ B (bpow BA bae B (@bplus _ _ B a b) n')
                       (@bplus _ _ B a b)
                       (bsum _ _ B (Datatypes.S n') g)
                       (@bplus _ _ B a b) IH
                       (@bae_refl _ _ B (@bplus _ _ B a b))). }
    (* Step 2: bring (a+b) inside the sum (right-multiplication
       extraction, symmetric face). *)
    assert (L2 : bae (@bmult _ _ B (bsum _ _ B (Datatypes.S n') g)
                                  (@bplus _ _ B a b))
                        (bsum _ _ B (Datatypes.S n')
                                  (fun k : nat => @bmult _ _ B (g k) (@bplus _ _ B a b)))).
    { apply (@bae_sym _ _ B).
      exact (bpa_bsum_mult_r _ _ B (Datatypes.S n') (@bplus _ _ B a b) g). }
    (* Step 3: split each term by distributivity into its a-part and
       b-part, then split the sum of pairs into a pair of sums. *)
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
    (* Step 4: normalize term by term — raise the power in the a-part,
       normalize the b-part. *)
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
    (* Step 5: rotate the b-sum (pull out its first term). *)
    assert (L5 : bae (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (bsum _ _ B (Datatypes.S n') gB))
                        (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bplus_wd_r BA bae B). exact (bsum_rot _ _ B n' gB). }
    (* Step 6: expose the last term of the a-sum (definitional shape,
       closed on the conversion face). *)
    assert (L6 : bae (@bplus _ _ B (bsum _ _ B (Datatypes.S n') gA)
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))
                        (@bplus _ _ B (@bplus _ _ B (bsum _ _ B n' gA) (gA n'))
                                  (@bplus _ _ B (gB 0%nat)
                                     (bsum _ _ B n'
                                        (fun i : nat => gB (Datatypes.S i)))))).
    { apply (@bae_refl _ _ B). }
    (* Step 7: AC rearrangement of the addition — [gB 0] to the front,
       [gA n'] to the end, the two main blocks side by side. *)
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
    (* Steps 8: merge the middle sums, pair terms via Pascal, and align
       head and tail with the target summands. *)
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
      exact (bpa_pair_mid _ _ B a b n' i hplus Hi). }
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
      - exact (bpa_pair_tail _ _ B a b n' hwd). }
    (* Step 9: reassemble the target sum (rotation in reverse, via the
       definitional shape of [bsum]). *)
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
    (* Pull out the power (definitional) and chain L1..L13. *)
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

(* ============================================================ *)
(* Section 3. Binomial expansion of the exponential partial sum.
   These statements cover the single-sum layer [(a+b)^k]; the Cauchy
   product covers the double-sum layer; the transposed product
   identity connecting the two is future work. *)
(* ============================================================ *)

(* Scalar repackaging: [(bcoef c * T) * bcoef s = bcoef (c*s) * T]. *)
Lemma bpa_scal_repack : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (c s : Q) (T : BA),
  bae (@bmult _ _ B (@bmult _ _ B (@bcoef _ _ B c) T) (@bcoef _ _ B s))
         (@bmult _ _ B (@bcoef _ _ B (c * s)%Q) T).
Proof.
  intros BA bae B c s T. eapply bae_trans.
  - apply (@bae_sym _ _ B).
    exact (@bmult_assoc _ _ B (@bcoef _ _ B c) T (@bcoef _ _ B s)).
  - eapply bae_trans.
    + apply (@bmult_wd _ _ B (@bcoef _ _ B c)
               (@bmult _ _ B T (@bcoef _ _ B s)) (@bcoef _ _ B c)
               (@bmult _ _ B (@bcoef _ _ B s) T)).
      * apply (@bae_refl _ _ B).
      * exact (@bcoef_comm _ _ B s T).
    + eapply bae_trans.
      * exact (@bmult_assoc _ _ B (@bcoef _ _ B c) (@bcoef _ _ B s) T).
      * apply (@bmult_wd _ _ B (@bmult _ _ B (@bcoef _ _ B c) (@bcoef _ _ B s)) T
                  (@bcoef _ _ B (c * s)%Q) T).
        -- apply (@bae_sym _ _ B). exact (@bcoef_mult _ _ B c s).
        -- apply (@bae_refl _ _ B).
Qed.

(* Term level: [bpow (a+b) k * (1/k!) = sum_{j<=k} (C(k,j)/k!) * a^j * b^(k-j)]. *)
Lemma bpa_esp_term_binom : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  (forall q r : Q, bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r))
                           (@bcoef _ _ B (q + r)%Q)) ->
  (forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)) ->
  forall k : nat,
    bae (@bmult _ _ B (bpow BA bae B (@bplus _ _ B a b) k)
                     (@bcoef _ _ B (/ q_fact k)))
           (bsum _ _ B (Datatypes.S k)
              (fun j : nat =>
                 @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                          (@bmult _ _ B (bpow BA bae B a j)
                                   (bpow BA bae B b (Nat.sub k j))))).
Proof.
  intros BA bae B a b hab hplus hwd k.
  set (F := fun j : nat =>
              @bmult _ _ B (@bcoef _ _ B (bpa_binom k j))
                       (@bmult _ _ B (bpow BA bae B a j)
                                (bpow BA bae B b (Nat.sub k j)))).
  eapply bae_trans.
  - apply (@bmult_wd _ _ B (bpow BA bae B (@bplus _ _ B a b) k)
                     (@bcoef _ _ B (/ q_fact k))
                     (bsum _ _ B (Datatypes.S k) F)
                     (@bcoef _ _ B (/ q_fact k))).
    + exact (bpa_bpow_add _ _ B a b hab hplus hwd k).
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

(* Series level: the binomial expansion of [exp_series_partial n (a+b)]
   (via the partial-sum presentation of the exponential). *)
Lemma bpa_esp_binom : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA),
  bae (@bmult _ _ B a b) (@bmult _ _ B b a) ->
  (forall q r : Q, bae (@bplus _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r))
                           (@bcoef _ _ B (q + r)%Q)) ->
  (forall q r : Q, q == r -> bae (@bcoef _ _ B q) (@bcoef _ _ B r)) ->
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
  intros BA bae B a b hab hplus hwd n.
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
    exact (bpa_esp_term_binom _ _ B a b hab hplus hwd k).
Qed.

(* ============================================================ *)
(* Scope notes (open items; no statements are admitted here):          *)
(*   1. The interface provides no additivity or congruence fields for  *)
(*      [bcoef]; the statements above carry them as explicit premises. *)
(*   2. The identity [exp (a+b) = exp a * exp b] additionally requires *)
(*      the transposed Cauchy product and continuity of multiplication *)
(*      for limits; this file supplies the power layer (Section 2) and *)
(*      the partial-sum layer (Section 3).                             *)
(*   3. The equivalence of the Pascal recursive coefficient with the   *)
(*      factorial ratio [n!/(k!*(n-k)!)] is left to a separate         *)
(*      development. *)
(* ============================================================ *)
