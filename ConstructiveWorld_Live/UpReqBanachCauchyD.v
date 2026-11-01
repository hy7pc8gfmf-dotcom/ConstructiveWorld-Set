(* ========================================================================== *)
(*  UpReqBanachCauchyD.v - Banach-Cauchy D: diagonal-triangle estimate for   *)
(*  double sums (the bxcd_ family).                                          *)
(*                                                                           *)
(*  使命：bxcd_ 族——bsum 折叠代数（pad_split/snoc/rev）、二项式项、F/G 范数  *)
(*  界、Q2_bound 对、乘积近一主定理 bxcd_prod_near_one（闭式 sigT 界）。     *)
(*  Mission: bsum folding algebra, binomial terms, F/G norm bounds, the      *)
(*  Q2_bound pair, and bxcd_prod_near_one: the product of the partial        *)
(*  exponential series of a and -a equals 1 + U with an explicit sigT bound. *)
(*                                                                           *)
(*  Ground: S-carrier wash of the Main-tree module of the same name.         *)
(*  Statement faces are Set-carried (Id / QeqT / QleT' / QltT / NatLe /     *)
(*  sigT); Prop atoms appear only inside proofs, through the gates           *)
(*  NatLe_drop, QleT'_to_Qle, QltT_to_Qlt, qeqT_imp_qeq; bare-equation      *)
(*  seams use the local id_eq_inv bridge (seat_abl12 precedent).             *)
(*                                                                           *)
(*  依赖：S01_BaseRing、S02_CauchyComplete、S03_QExp、UpReqBanachExp、       *)
(*  UpReqBanachProd、UpReqBanachDouble、UpReqBanachExpBasic、                *)
(*  UpReqBanachAdd、UpReqNormConv、UpReqBanachProd2、UpReqBanachInvPre、     *)
(*  BanachNoHyp；Stdlib QArith、Arith、ZArith、Setoid、Morphisms、Lia。      *)
(*                                                                           *)
(*  构造性：全件 Qed 闭合、零承认词面、无经典逻辑；语句面 Set 承载，         *)
(*  Prop 仅存证明体内（门桥见上）。                                          *)
(*                                                                           *)
(*  编译配方：rocq c -native-compiler no -Q . "" UpReqBanachCauchyD.v        *)
(*  （Rocq 9.1 toolchain、cpu_guard 包裹同世界影子重编）。                   *)
(* ========================================================================== *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachDouble.
Require Import UpReqBanachExpBasic.
Require Import UpReqBanachAdd.
Require Import UpReqNormConv.
Require Import UpReqBanachProd2.
Require Import UpReqBanachInvPre.
Require Import BanachNoHyp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith ZArith.ZArith.
From Stdlib Require Import Setoid Morphisms.
From Stdlib Require Import Lia.

(* Id inversion bridge: the only constructor is id_refl, so Id x y carries
   x = y. Proof-internal extraction used at the bare-equation seams only
   (mirrors the seat_abl12 precedent); statements stay Id-carried. *)
Definition id_eq_inv {A : Set} {x y : A} (H : Id x y) : x = y :=
  match H with id_refl => eq_refl end.

(* Series term families: F a k := a^k/k!, G a k := (-a)^k/k! *)
Definition bxcd_F (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                  (a : BA) (k : nat) : BA :=
  @bmult _ _ B (bpow _ _ B a k) (@bcoef _ _ B (/ q_fact k)).

Definition bxcd_G (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                  (a : BA) (k : nat) : BA :=
  @bmult _ _ B (bpow _ _ B (@bopp _ _ B a) k) (@bcoef _ _ B (/ q_fact k)).

(* Q term family: A c k := c^k/k! *)
Definition bxcd_A (c : Q) (k : nat) : Q := (q_pow c k / q_fact k)%Q.

(* Remainder (square minus triangle): within row j, the sum of the
   off-diagonal terms with i > n-j *)
Definition bxcd_U (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                  (a : BA) (n : nat) : BA :=
  bsum _ _ B (Datatypes.S n)
    (fun j : nat => bsum _ _ B (Datatypes.S n)
       (fun i : nat =>
          if Nat.ltb (n - j) i
          then @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)
          else @bzero _ _ B)).

(* ============================================================ *)
(* 1. Small carrier-equality algebra                             *)
(* ============================================================ *)

Lemma bxcd_bsum_zero : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (n : nat) (f : nat -> BA),
  (forall k : nat, bae (f k) (@bzero _ _ B)) ->
  bae (bsum _ _ B n f) (@bzero _ _ B).
Proof.
  intros BA bae B n f Hf. induction n as [| m IH].
  - apply (@bae_refl _ _ B).
  - change (bsum _ _ B (Datatypes.S m) f) with (@bplus _ _ B (bsum _ _ B m f) (f m)).
    eapply bae_trans.
    + apply (@bplus_wd_l _ _ B (bsum _ _ B m f) (@bzero _ _ B) (f m)).
      exact IH.
    + eapply bae_trans.
      * exact (@bplus_zero_l _ _ B (f m)).
      * exact (Hf m).
Qed.

(* Sum splitting (zero padding): sum_{j<=n} F j == sum_{j<=m} F j
   + sum_{j<=n} [m<j] F j *)
Lemma bxcd_bsum_pad_split : forall (BA : Set) (bae : BA -> BA -> Set)
                                   (B : BanachAlg BA bae) (m n : nat)
                                   (F : nat -> BA),
  NatLe m n ->
  bae (bsum _ _ B (Datatypes.S n) F)
         (@bplus _ _ B (bsum _ _ B (Datatypes.S m) F)
                   (bsum _ _ B (Datatypes.S n)
                      (fun j : nat =>
                         if Nat.ltb m j then F j else @bzero _ _ B))).
Proof.
  intros BA bae B m n F Hmn. revert Hmn. induction n as [| n' IH]; intros Hmn.
  - pose proof (NatLe_drop _ _ Hmn) as Hmle.
    assert (Hm : m = 0%nat) by lia. subst m.
    apply (@bae_sym _ _ B).
    eapply bae_trans.
    + apply (@bplus_wd_r _ _ B (@bplus _ _ B (@bzero _ _ B) (@bzero _ _ B))
                           (@bzero _ _ B)
                           (@bplus _ _ B (@bzero _ _ B) (F 0%nat))).
      exact (@bplus_zero_l _ _ B (@bzero _ _ B)).
    + exact (@bplus_zero _ _ B (@bplus _ _ B (@bzero _ _ B) (F 0%nat))).
  - pose proof (NatLe_drop _ _ Hmn) as Hmle.
    destruct (Nat.eq_dec m (Datatypes.S n')) as [Heq | Hne].
    + subst m.
      assert (Hp : bae (bsum _ _ B (Datatypes.S (Datatypes.S n'))
                  (fun j : nat =>
                     if Nat.ltb (Datatypes.S n') j then F j else @bzero _ _ B))
                  (@bzero _ _ B)).
      { eapply bae_trans.
        - apply (bsum_ext _ _ B (Datatypes.S (Datatypes.S n'))
                  (fun j : nat =>
                     if Nat.ltb (Datatypes.S n') j then F j else @bzero _ _ B)
                  (fun j : nat => @bzero _ _ B)).
          intros k Hk.
          destruct (Nat.ltb (Datatypes.S n') k) eqn:Ek.
          + apply Nat.ltb_lt in Ek. exfalso. lia.
          + apply (@bae_refl _ _ B).
        - apply (bxcd_bsum_zero _ _ B _ (fun j : nat => @bzero _ _ B)).
          intros k. apply (@bae_refl _ _ B). }
      eapply bae_trans.
      * apply (@bae_sym _ _ B).
        eapply bae_trans.
        -- apply (@bplus_wd_r _ _ B (bsum _ _ B (Datatypes.S (Datatypes.S n'))
                                   (fun j : nat =>
                                      if Nat.ltb (Datatypes.S n') j
                                      then F j else @bzero _ _ B))
                           (@bzero _ _ B)
                           (bsum _ _ B (Datatypes.S (Datatypes.S n')) F)).
           exact Hp.
        -- exact (@bplus_zero _ _ B (bsum _ _ B (Datatypes.S (Datatypes.S n')) F)).
      * apply (@bae_refl _ _ B).
    + assert (Hmlt : Nat.ltb m (Datatypes.S n') = true)
        by (apply Nat.ltb_lt; lia).
      assert (Hmn' : (m <= n')%nat) by lia.
      assert (HmnL : NatLe m n') by (apply NatLe_lift; exact Hmn').
      change (bsum _ _ B (Datatypes.S (Datatypes.S n')) F)
        with (@bplus _ _ B (bsum _ _ B (Datatypes.S n') F) (F (Datatypes.S n'))).
      change (bsum _ _ B (Datatypes.S (Datatypes.S n'))
                (fun j : nat => if Nat.ltb m j then F j else @bzero _ _ B))
        with (@bplus _ _ B (bsum _ _ B (Datatypes.S n')
                          (fun j : nat => if Nat.ltb m j then F j else @bzero _ _ B))
                       (if Nat.ltb m (Datatypes.S n')
                        then F (Datatypes.S n') else @bzero _ _ B)).
      rewrite Hmlt.
      eapply bae_trans.
      * apply (@bplus_wd_l _ _ B). exact (IH HmnL).
      * apply (@bae_sym _ _ B).
        exact (@bplus_assoc _ _ B (bsum _ _ B (Datatypes.S m) F)
                (bsum _ _ B (Datatypes.S n')
                   (fun j : nat => if Nat.ltb m j then F j else @bzero _ _ B))
                (F (Datatypes.S n'))).
Qed.
(* Tail term extraction (definitional): sum_{j<=S n} f j == (sum_{j<n} f j) + f n *)
Lemma bxcd_bsum_snoc : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (n : nat) (f : nat -> BA),
  bae (bsum _ _ B (Datatypes.S n) f) (@bplus _ _ B (bsum _ _ B n f) (f n)).
Proof.
  intros BA bae B n f. apply (@bae_refl _ _ B).
Qed.

(* Sum reversal: sum_{j<=n} h j == sum_{j<=n} h (n-j) *)
Lemma bxcd_bsum_rev : forall (BA : Set) (bae : BA -> BA -> Set)
                             (B : BanachAlg BA bae) (n : nat) (h : nat -> BA),
  bae (bsum _ _ B (Datatypes.S n) h)
         (bsum _ _ B (Datatypes.S n) (fun j : nat => h (Nat.sub n j))).
Proof.
  intros BA bae B n. induction n as [| n' IH]; intros h.
  - apply (@bae_refl _ _ B).
  - (* middle piece M := h (S n') + sum_{k<=n'} h (n'-k) *)
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (h (Datatypes.S n'))
                (bsum _ _ B (Datatypes.S n')
                   (fun k : nat => h (Nat.sub n' k)))) _).
    + eapply bae_trans.
      * apply (@bplus_comm _ _ B (bsum _ _ B (Datatypes.S n') h)
                              (h (Datatypes.S n'))).
      * apply (@bplus_wd_r _ _ B (bsum _ _ B (Datatypes.S n') h)
                 (bsum _ _ B (Datatypes.S n')
                    (fun k : nat => h (Nat.sub n' k)))
                 (h (Datatypes.S n'))).
        exact (IH h).
    + (* h (S n') + sum_{k<=n'} h (n'-k) == sum_{j<=S n'} h (S n'-j) (rot) *)
      apply (@bae_sym _ _ B).
      apply (@bsum_rot _ _ B (Datatypes.S n')
               (fun j : nat => h (Nat.sub (Datatypes.S n') j))).
Qed.
(* Diagonal block == the sum: dline i k == sum_{t<=k} F(i+k-t) G t *)
Lemma bxcd_dline_bsum : forall (BA : Set) (bae : BA -> BA -> Set)
                               (B : BanachAlg BA bae)
                               (F G : nat -> BA) (i k : nat),
  bae (bd2_dline _ _ B F G i k)
         (bsum _ _ B (Datatypes.S k)
            (fun t : nat =>
               @bmult _ _ B (F (Nat.add i (Nat.sub k t))) (G t))).
Proof.
  intros BA bae B F G i k. revert i. induction k as [| m IH]; intros i.
  - assert (Hi : ((Nat.add i (Nat.sub 0%nat 0%nat)) = i)%nat) by lia.
    change (bsum _ _ B (Datatypes.S 0%nat)
              (fun t : nat => @bmult _ _ B (F (Nat.add i (Nat.sub 0%nat t))) (G t)))
      with (@bplus _ _ B (@bzero _ _ B)
              (@bmult _ _ B (F (Nat.add i (Nat.sub 0%nat 0%nat))) (G 0%nat))).
    rewrite Hi.
    apply (@bae_sym _ _ B).
    apply (@bplus_zero_l _ _ B (@bmult _ _ B (F i) (G 0%nat))).
  - change (bd2_dline _ _ B F G i (Datatypes.S m))
      with (@bplus _ _ B (@bmult _ _ B (F i) (G (Datatypes.S m)))
                     (bd2_dline _ _ B F G (Datatypes.S i) m)).
    change (bsum _ _ B (Datatypes.S (Datatypes.S m))
              (fun t : nat => @bmult _ _ B (F (Nat.add i (Nat.sub (Datatypes.S m) t)))
                                       (G t)))
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S m)
                       (fun t : nat =>
                          @bmult _ _ B (F (Nat.add i (Nat.sub (Datatypes.S m) t)))
                                   (G t)))
                     (@bmult _ _ B (F (Nat.add i (Nat.sub (Datatypes.S m) (Datatypes.S m))))
                              (G (Datatypes.S m)))).
    assert (Hi0 : ((Nat.add i (Nat.sub (Datatypes.S m) (Datatypes.S m))) = i)%nat) by lia.
    rewrite Hi0.
    apply (@bae_trans _ _ B _
      (@bplus _ _ B (@bmult _ _ B (F i) (G (Datatypes.S m)))
                (bsum _ _ B (Datatypes.S m)
                   (fun t : nat =>
                      @bmult _ _ B (F (Nat.add (Datatypes.S i) (Nat.sub m t)))
                               (G t)))) _).
    + apply (@bplus_wd_r _ _ B (bd2_dline _ _ B F G (Datatypes.S i) m)
                           (bsum _ _ B (Datatypes.S m)
                              (fun t : nat =>
                                 @bmult _ _ B (F (Nat.add (Datatypes.S i)
                                                      (Nat.sub m t)))
                                          (G t)))
                           (@bmult _ _ B (F i) (G (Datatypes.S m)))).
      exact (IH (Datatypes.S i)).
    + eapply bae_trans.
      * apply (@bplus_wd_r _ _ B
                 (bsum _ _ B (Datatypes.S m)
                    (fun t : nat =>
                       @bmult _ _ B (F (Nat.add (Datatypes.S i) (Nat.sub m t)))
                                (G t)))
                 (bsum _ _ B (Datatypes.S m)
                    (fun t : nat =>
                       @bmult _ _ B (F (Nat.add i (Nat.sub (Datatypes.S m) t)))
                                (G t)))
                 (@bmult _ _ B (F i) (G (Datatypes.S m)))).
        apply (bsum_ext _ _ B (Datatypes.S m)
          (fun t : nat =>
             @bmult _ _ B (F (Nat.add (Datatypes.S i) (Nat.sub m t))) (G t))
          (fun t : nat =>
             @bmult _ _ B (F (Nat.add i (Nat.sub (Datatypes.S m) t))) (G t))).
        intros t Ht.
        assert (Hij : (Nat.add (Datatypes.S i) (Nat.sub m t))
                      = (Nat.add i (Nat.sub (Datatypes.S m) t))) by lia.
        rewrite Hij.
        apply (@bae_refl _ _ B).
      * apply (@bplus_comm _ _ B (@bmult _ _ B (F i) (G (Datatypes.S m)))
                             (bsum _ _ B (Datatypes.S m)
                                (fun t : nat =>
                                   @bmult _ _ B (F (Nat.add i
                                                      (Nat.sub (Datatypes.S m) t)))
                                            (G t)))).
Qed.

(* diagf == bsum (same recursion shape) *)
Lemma bxcd_diagf_bsum : forall (BA : Set) (bae : BA -> BA -> Set)
                               (B : BanachAlg BA bae)
                               (F G : nat -> BA) (i n : nat),
  bae (bd2_diagf _ _ B F G i n)
         (bsum _ _ B (Datatypes.S n)
            (fun k : nat => bd2_dline _ _ B F G i k)).
Proof.
  intros BA bae B F G i n. induction n as [| m IH].
  - apply (@bae_sym _ _ B).
    apply (@bplus_zero_l _ _ B (bd2_dline _ _ B F G i 0%nat)).
  - change (bd2_diagf _ _ B F G i (Datatypes.S m))
      with (@bplus _ _ B (bd2_diagf _ _ B F G i m)
                     (bd2_dline _ _ B F G i (Datatypes.S m))).
    change (bsum _ _ B (Datatypes.S (Datatypes.S m))
              (fun k : nat => bd2_dline _ _ B F G i k))
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S m)
                          (fun k : nat => bd2_dline _ _ B F G i k))
                     (bd2_dline _ _ B F G i (Datatypes.S m))).
    apply (@bplus_wd_l _ _ B). exact IH.
Qed.

(* ============================================================ *)
(* 2. Scalar recentering (via the Prod2 bpr2_bterm_split;        *)
(*    zero new proof work)                                       *)
(* ============================================================ *)

(* Term level: F a j G a i == (a^j (-a)^i) bcoef(/j! /i!)
   -- the seven-step scalar-centering chain delivered by Prod2
   (the a^j b^i product order is left untouched), directly
   specialized. *)
Lemma bxcd_scal_term : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (a : BA) (j i : nat),
  bae (@bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i))
         (@bmult _ _ B (@bmult _ _ B (bpow _ _ B a j) (bpow _ _ B (@bopp _ _ B a) i))
                   (@bcoef _ _ B (Qinv (q_fact j) * Qinv (q_fact i))%Q)).
Proof.
  intros BA bae B a j i.
  unfold bxcd_F, bxcd_G.
  assert (Hs := bpr2_bterm_split _ _ B a (@bopp _ _ B a) (Nat.add j i) j).
  assert (Hij : (Nat.sub (Nat.add j i) j = i)%nat) by lia.
  rewrite Hij in Hs.
  exact Hs.
Qed.

(* ============================================================ *)
(* 3. Q-layer coefficient bridges (Pascal <-> factorial: the     *)
(*    bpa_binom out-of-range / diagonal collapse segments)       *)
(* ============================================================ *)

(* Binomial positivity (j <= k; paired induction, the out-of-range
   and diagonal boundary cases collapse) *)
Lemma bxcd_binom_pos : forall k j : nat, NatLe j k -> QltT 0 (bpa_binom k j).
Proof.
  induction k as [| k' IH]; intros j Hj.
  - pose proof (NatLe_drop _ _ Hj) as Hjle.
    assert (Hj0 : j = 0%nat) by lia. subst j.
    exact (q_fact_pos 0%nat).
  - pose proof (NatLe_drop _ _ Hj) as Hjle.
    destruct (Nat.eq_dec j (Datatypes.S k')) as [Heq | Hne].
    + subst j.
      apply Qlt_to_QltT.
      change (bpa_binom (Datatypes.S k') (Datatypes.S k'))
        with ((bpa_binom k' k' + bpa_binom k' (Datatypes.S k'))%Q).
      rewrite (qeqT_imp_qeq _ _ (bpa_binom_out k' (Datatypes.S k') ltac:(lia))).
      rewrite (qeqT_imp_qeq _ _ (bpa_binom_diag k')).
      exact (QltT_to_Qlt _ _ (q_fact_pos 0%nat)).
    + destruct j as [| j'].
      * exact (q_fact_pos 0%nat).
      * change (bpa_binom (Datatypes.S k') (Datatypes.S j'))
          with ((bpa_binom k' j' + bpa_binom k' (Datatypes.S j'))%Q).
        apply Qlt_to_QltT.
        apply (Qplus_lt_compat 0%Q (bpa_binom k' j') 0%Q
                 (bpa_binom k' (Datatypes.S j'))
                 (QltT_to_Qlt _ _ (IH j' ltac:(apply NatLe_lift; lia)))
                 (QltT_to_Qlt _ _
                    (IH (Datatypes.S j') ltac:(apply NatLe_lift; lia)))).
Qed.

(* Integral bridge: C(k,j) j! (k-j)! == k! (j <= k; two induction
   hypotheses, Z-coefficient merging by ring) *)
Lemma bxcd_binom_fact2 : forall k j : nat, NatLe j k ->
  QeqT ((bpa_binom k j * q_fact j) * q_fact (Nat.sub k j)) (q_fact k).
Proof.
  induction k as [| k' IH]; intros j Hj; apply qeq_imp_qeqT.
  - pose proof (NatLe_drop _ _ Hj) as Hjle.
    assert (Hj0 : j = 0%nat) by lia. subst j. reflexivity.
  - pose proof (NatLe_drop _ _ Hj) as Hjle.
    destruct (Nat.eq_dec j (Datatypes.S k')) as [Heq | Hne].
    + subst j.
      change (bpa_binom (Datatypes.S k') (Datatypes.S k'))
        with ((bpa_binom k' k' + bpa_binom k' (Datatypes.S k'))%Q).
      rewrite (qeqT_imp_qeq _ _ (bpa_binom_out k' (Datatypes.S k') ltac:(lia))).
      rewrite (qeqT_imp_qeq _ _ (bpa_binom_diag k')).
      assert (Hz0 : Nat.sub (Datatypes.S k') (Datatypes.S k') = 0%nat) by lia.
      rewrite Hz0.
      change (q_fact 0%nat) with 1%Q.
      ring.
    + destruct j as [| j'].
      * assert (Hs : (Nat.sub (Datatypes.S k') 0%nat) = (Datatypes.S k')) by lia.
        rewrite Hs.
        change (bpa_binom (Datatypes.S k') 0%nat) with 1%Q.
        change (q_fact 0%nat) with 1%Q.
        ring.
      * change (bpa_binom (Datatypes.S k') (Datatypes.S j'))
          with ((bpa_binom k' j' + bpa_binom k' (Datatypes.S j'))%Q).
        assert (Hjk : (Datatypes.S j' <= k')%nat) by lia.
        assert (Hrk : (Nat.sub k' j' = Datatypes.S (Nat.sub k' (Datatypes.S j')))) by lia.
        assert (Hrk' : Nat.sub (Datatypes.S k') (Datatypes.S j')
                       = Datatypes.S (Nat.sub k' (Datatypes.S j'))) by lia.
        assert (IH1 : ((bpa_binom k' j' * q_fact j')
                       * q_fact (Nat.sub k' j') == q_fact k')%Q)
          by (apply qeqT_imp_qeq; exact (IH j' ltac:(apply NatLe_lift; lia))).
        assert (IH2 : ((bpa_binom k' (Datatypes.S j') * q_fact (Datatypes.S j'))
                       * q_fact (Nat.sub k' (Datatypes.S j')) == q_fact k')%Q)
          by (apply qeqT_imp_qeq;
                exact (IH (Datatypes.S j') ltac:(apply NatLe_lift; exact Hjk))).
        rewrite Hrk in IH1. rewrite Hrk'.
        change (q_fact (Datatypes.S j'))
          with ((Z.of_nat (Datatypes.S j') # 1) * q_fact j')%Q.
        change (q_fact (Datatypes.S j'))
          with ((Z.of_nat (Datatypes.S j') # 1) * q_fact j')%Q in IH2.
        change (q_fact (Datatypes.S (Nat.sub k' (Datatypes.S j'))))
          with ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))) # 1)
                * q_fact (Nat.sub k' (Datatypes.S j')))%Q.
        change (q_fact (Datatypes.S (Nat.sub k' (Datatypes.S j'))))
          with ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))) # 1)
                * q_fact (Nat.sub k' (Datatypes.S j')))%Q in IH1.
        change (q_fact (Datatypes.S k'))
          with ((Z.of_nat (Datatypes.S k') # 1) * q_fact k')%Q.
        assert (Hn1 : (Nat.sub k' (Datatypes.S j') + Datatypes.S j')%nat
                      = k')
          by (apply Nat.sub_add; exact Hjk).
        assert (Hz : (Z.of_nat (Datatypes.S j')
                      + Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))))%Z
                     = Z.of_nat (Datatypes.S k')).
        { assert (Hn : (Datatypes.S j'
                        + Datatypes.S (Nat.sub k' (Datatypes.S j')))%nat
                       = Datatypes.S k').
          { rewrite (Nat.add_succ_r (Datatypes.S j')
                      (Nat.sub k' (Datatypes.S j'))).
            apply f_equal.
            rewrite (Nat.add_comm (Datatypes.S j')
                      (Nat.sub k' (Datatypes.S j'))).
            exact Hn1. }
          rewrite <- Nat2Z.inj_add. rewrite Hn. reflexivity. }
        assert (Hz2 : ((Z.of_nat (Datatypes.S j') # 1)
                       + (Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j'))) # 1))%Q
                      == (Z.of_nat (Datatypes.S k') # 1)%Q).
        { unfold Qeq. cbn [Qnum Qden Qplus].
          repeat rewrite Z.mul_1_l. repeat rewrite Z.mul_1_r.
          rewrite Hz. reflexivity. }
        transitivity (((bpa_binom k' j' * ((Z.of_nat (Datatypes.S j') # 1)
                                            * q_fact j'))
                       * ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1) * q_fact (Nat.sub k' (Datatypes.S j'))))
                      + (bpa_binom k' (Datatypes.S j')
                         * ((Z.of_nat (Datatypes.S j') # 1) * q_fact j'))
                       * ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1) * q_fact (Nat.sub k' (Datatypes.S j'))))%Q.
        { ring. }
        transitivity ((((bpa_binom k' j' * q_fact j')
                        * ((Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                            # 1) * q_fact (Nat.sub k' (Datatypes.S j'))))
                       * (Z.of_nat (Datatypes.S j') # 1))
                      + ((bpa_binom k' (Datatypes.S j')
                            * ((Z.of_nat (Datatypes.S j') # 1) * q_fact j'))
                         * q_fact (Nat.sub k' (Datatypes.S j')))
                       * (Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1))%Q.
        { ring. }
        rewrite IH1. rewrite IH2.
        transitivity (((Z.of_nat (Datatypes.S j') # 1)
                       + (Z.of_nat (Datatypes.S (Nat.sub k' (Datatypes.S j')))
                           # 1)) * q_fact k')%Q.
        { ring. }
        rewrite Hz2. reflexivity.
Qed.

(* Reciprocal bridge: C(k,j) /k! == /j! /(k-j)! (j <= k; fact2 plus
   a four-step right cancellation) *)
Lemma bxcd_binom_fact : forall k j : nat, NatLe j k ->
  QeqT ((bpa_binom k j * / q_fact k)) (/ q_fact j * / q_fact (Nat.sub k j)).
Proof.
  intros k j Hj.
  pose proof (NatLe_drop _ _ Hj) as Hjle.
  apply qeq_imp_qeqT.
  assert (H2 : ((bpa_binom k j * q_fact j) * q_fact (Nat.sub k j) == q_fact k)%Q)
    by (apply qeqT_imp_qeq; exact (bxcd_binom_fact2 k j Hj)).
  assert (HLXT : QltT 0 ((q_fact j * q_fact (Nat.sub k j))%Q))
    by (apply ncv_qmult_lt0; apply QltT_to_Qlt; apply q_fact_pos).
  assert (HX : ~ ((q_fact j * q_fact (Nat.sub k j))%Q == 0)).
  { intro Hq.
    exact (Qlt_not_eq 0 ((q_fact j * q_fact (Nat.sub k j))%Q)
             (QltT_to_Qlt _ _ HLXT) (Qeq_sym _ _ Hq)). }
  assert (HY : ~ (q_fact k == 0)).
  { intro Hq.
    exact (Qlt_not_eq 0 (q_fact k) (QltT_to_Qlt _ _ (q_fact_pos k))
             (Qeq_sym _ _ Hq)). }
  transitivity (((bpa_binom k j * / q_fact k) * 1)%Q).
  { symmetry. apply Qmult_1_r. }
  transitivity (((bpa_binom k j * / q_fact k)
                 * ((q_fact j * q_fact (Nat.sub k j))
                    * / (q_fact j * q_fact (Nat.sub k j)))))%Q.
  { rewrite <- (Qmult_inv_r (q_fact j * q_fact (Nat.sub k j))%Q HX).
    reflexivity. }
  transitivity ((((bpa_binom k j * q_fact j) * q_fact (Nat.sub k j))
                 * / q_fact k)
                * / (q_fact j * q_fact (Nat.sub k j)))%Q.
  { ring. }
  rewrite H2.
  transitivity (((q_fact k * / q_fact k)
                 * / (q_fact j * q_fact (Nat.sub k j))))%Q.
  { ring. }
  rewrite (Qmult_inv_r (q_fact k) HY).
  transitivity ((/ (q_fact j * q_fact (Nat.sub k j)))%Q).
  { apply Qmult_1_l. }
  apply Qinv_mult_distr.
Qed.

(* ============================================================ *)
(* 4. Square decomposition: P == bone + U (Cauchy square to      *)
(*    triangle collapse to the remainder term)                   *)
(* ============================================================ *)

Definition bxcd_T (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
                  (a : BA) (n : nat) : BA :=
  bsum _ _ B (Datatypes.S n)
    (fun j : nat => bsum _ _ B (Datatypes.S (Nat.sub n j))
       (fun i : nat => @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i))).

(* Diagonal block == binomial row: dline -> reversal -> per-term
   scalar bridge -> binomial row *)
Lemma bxcd_dline_binom_term : forall (BA : Set) (bae : BA -> BA -> Set)
                                     (B : BanachAlg BA bae) (a : BA),
  forall k : nat,
    bae (bd2_dline _ _ B (bxcd_F _ _ B a) (bxcd_G _ _ B a) 0%nat k)
           (@bmult _ _ B (bpow _ _ B (@bplus _ _ B a (@bopp _ _ B a)) k)
                     (@bcoef _ _ B (/ q_fact k))).
Proof.
  intros BA bae B a k.
  apply (@bae_trans _ _ B _
    (bsum _ _ B (Datatypes.S k)
       (fun j : nat =>
          @bmult _ _ B (@bcoef _ _ B (bpa_binom k j * / q_fact k)%Q)
                   (@bmult _ _ B (bpow _ _ B a j)
                             (bpow _ _ B (@bopp _ _ B a) (Nat.sub k j))))) _).
  - apply (@bae_trans _ _ B _
      (bsum _ _ B (Datatypes.S k)
         (fun t : nat =>
            @bmult _ _ B (bxcd_F _ _ B a (Nat.sub k t)) (bxcd_G _ _ B a t))) _).
    + exact (bxcd_dline_bsum _ _ B (bxcd_F _ _ B a) (bxcd_G _ _ B a) 0%nat k).
    + apply (@bae_trans _ _ B _
        (bsum _ _ B (Datatypes.S k)
           (fun j : nat =>
              @bmult _ _ B (bxcd_F _ _ B a (Nat.sub k (Nat.sub k j)))
                       (bxcd_G _ _ B a (Nat.sub k j)))) _).
      * exact (bxcd_bsum_rev _ _ B k
                  (fun x : nat =>
                     @bmult _ _ B (bxcd_F _ _ B a (Nat.sub k x)) (bxcd_G _ _ B a x))).
      * apply bsum_ext. intros j Hj.
        assert (Hkj : ((Nat.sub k (Nat.sub k j)) = j)%nat) by lia.
        rewrite Hkj.
        eapply bae_trans.
        -- exact (bxcd_scal_term _ _ B a j (Nat.sub k j)).
        -- apply (@bae_trans _ _ B _
              (@bmult _ _ B (@bcoef _ _ B (Qinv (q_fact j)
                                        * Qinv (q_fact (Nat.sub k j)))%Q)
                        (@bmult _ _ B (bpow _ _ B a j)
                                  (bpow _ _ B (@bopp _ _ B a) (Nat.sub k j)))) _).
           ++ exact (@bcoef_comm _ _ B
                       (Qinv (q_fact j) * Qinv (q_fact (Nat.sub k j)))%Q
                       (@bmult _ _ B (bpow _ _ B a j)
                                (bpow _ _ B (@bopp _ _ B a) (Nat.sub k j)))).
           ++ apply (@bpr2_bmult_wd_l _ _ B _ _ _).
              apply (@bcoef_wd _ _ B).
              apply qeqT_sym_hw.
              exact (bxcd_binom_fact k j ltac:(apply NatLe_lift; lia)).
  - apply (@bae_sym _ _ B).
    exact (bnh_esp_term_binom _ _ B a (@bopp _ _ B a)
             (binv_mult_opp_swap _ _ B a) k).
Qed.

(* Triangle sum == the unit *)
Lemma bxcd_tri_bone : forall (BA : Set) (bae : BA -> BA -> Set)
                             (B : BanachAlg BA bae) (a : BA),
  forall n : nat, bae (bxcd_T _ _ B a n) (@bone _ _ B).
Proof.
  intros BA bae B a n.
  apply (@bae_trans _ _ B _ (bd2_tri _ _ B n (bxcd_F _ _ B a) (bxcd_G _ _ B a)) _).
  - apply (@bae_sym _ _ B).
    apply (@bae_trans _ _ B _
      (bsum _ _ B (Datatypes.S n)
         (fun i : nat => @bmult _ _ B (bxcd_F _ _ B a i)
                    (bsum _ _ B (Datatypes.S (Nat.sub n i)) (bxcd_G _ _ B a)))) _).
    + exact (bd2_tri_eq_rect_row _ _ B n (bxcd_F _ _ B a) (bxcd_G _ _ B a)).
    + apply bsum_ext. intros j _.
      apply (@bae_sym _ _ B).
      exact (bsum_mult_l _ _ B (Datatypes.S (Nat.sub n j)) (bxcd_F _ _ B a j)
               (bxcd_G _ _ B a)).
  - apply (@bae_trans _ _ B _ (bd2_diag _ _ B n (bxcd_F _ _ B a) (bxcd_G _ _ B a)) _).
    + exact (bd2_tri_eq_diag _ _ B n (bxcd_F _ _ B a) (bxcd_G _ _ B a)).
    + apply (@bae_trans _ _ B _
        (exp_series_partial _ _ B (@bplus _ _ B a (@bopp _ _ B a)) n) _).
      * apply (@bae_trans _ _ B _
          (bsum _ _ B (Datatypes.S n)
             (fun k : nat =>
                bd2_dline _ _ B (bxcd_F _ _ B a) (bxcd_G _ _ B a) 0%nat k)) _).
        -- exact (bxcd_diagf_bsum _ _ B (bxcd_F _ _ B a) (bxcd_G _ _ B a) 0%nat n).
        -- apply (@bae_trans _ _ B _
              (bsum _ _ B (Datatypes.S n)
                 (fun k : nat =>
                    @bmult _ _ B (bpow _ _ B (@bplus _ _ B a (@bopp _ _ B a)) k)
                              (@bcoef _ _ B (/ q_fact k)))) _).
           ++ apply (@bsum_ext _ _ B (Datatypes.S n)
                 (fun k : nat => bd2_dline _ _ B (bxcd_F _ _ B a) (bxcd_G _ _ B a) 0%nat k)
                 (fun k : nat =>
                    @bmult _ _ B (bpow _ _ B (@bplus _ _ B a (@bopp _ _ B a)) k)
                              (@bcoef _ _ B (/ q_fact k)))).
              intros k _.
              exact (bxcd_dline_binom_term _ _ B a k).
           ++ apply (@bae_sym _ _ B).
              exact (esp_as_bsum _ _ B (@bplus _ _ B a (@bopp _ _ B a)) n).
      * exact (binv_esp_opp_add _ _ B a n).
Qed.

(* Main decomposition: P == bone + U *)
Lemma bxcd_prod_split : forall (BA : Set) (bae : BA -> BA -> Set)
                               (B : BanachAlg BA bae) (a : BA),
  forall n : nat,
    bae (@bmult _ _ B (exp_series_partial _ _ B a n)
                     (exp_series_partial _ _ B (@bopp _ _ B a) n))
           (@bplus _ _ B (@bone _ _ B) (bxcd_U _ _ B a n)).
Proof.
  intros BA bae B a n.
  apply (@bae_trans _ _ B _
    (bsum _ _ B (Datatypes.S n)
       (fun j : nat => bsum _ _ B (Datatypes.S n)
          (fun i : nat => @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)))) _).
  { exact (esp_prod_square _ _ B a (@bopp _ _ B a) n). }
  apply (@bae_trans _ _ B _
    (bsum _ _ B (Datatypes.S n)
       (fun j : nat =>
          @bplus _ _ B (bsum _ _ B (Datatypes.S (Nat.sub n j))
                      (fun i : nat => @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)))
                   (bsum _ _ B (Datatypes.S n)
                      (fun i : nat =>
                         if Nat.ltb (Nat.sub n j) i
                         then @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)
                         else @bzero _ _ B)))) _).
  { apply bsum_ext. intros j _. apply bxcd_bsum_pad_split. apply NatLe_lift. lia. }
  apply (@bae_trans _ _ B _ (@bplus _ _ B (bxcd_T _ _ B a n) (bxcd_U _ _ B a n)) _).
  { exact (bsum_plus _ _ B (Datatypes.S n)
             (fun j : nat => bsum _ _ B (Datatypes.S (Nat.sub n j))
                              (fun i : nat => @bmult _ _ B (bxcd_F _ _ B a j)
                                                (bxcd_G _ _ B a i)))
             (fun j : nat => bsum _ _ B (Datatypes.S n)
                              (fun i : nat =>
                                 if Nat.ltb (Nat.sub n j) i
                                 then @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)
                                 else @bzero _ _ B))). }
  apply (@bplus_wd_l _ _ B (bxcd_T _ _ B a n) (@bone _ _ B) (bxcd_U _ _ B a n)).
  exact (bxcd_tri_bone _ _ B a n).
Qed.

(* Norm bridge: bae P (bone+U) implies norm(P-bone) QeqT norm(U) *)
Lemma bxcd_prod_close : forall (BA : Set) (bae : BA -> BA -> Set)
                               (B : BanachAlg BA bae) (a : BA) (n : nat)
                               (U : BA),
  bae (@bmult _ _ B (exp_series_partial _ _ B a n)
                   (exp_series_partial _ _ B (@bopp _ _ B a) n))
         (@bplus _ _ B (@bone _ _ B) U) ->
  QeqT (@bnorm _ _ B (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                    (exp_series_partial _ _ B (@bopp _ _ B a) n))
                          (@bopp _ _ B (@bone _ _ B)))) (@bnorm _ _ B U).
Proof.
  intros BA bae B a n U H. apply (@bnorm_wd _ _ B).
  eapply bae_trans.
  { exact (@bplus_wd _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                              (exp_series_partial _ _ B (@bopp _ _ B a) n))
                       (@bopp _ _ B (@bone _ _ B))
                       (@bplus _ _ B (@bone _ _ B) U) (@bopp _ _ B (@bone _ _ B))
                       H (@bae_refl _ _ B (@bopp _ _ B (@bone _ _ B)))). }
  apply (@bae_trans _ _ B _ (@bplus _ _ B (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B))) U) _).
  { exact (@bplus_middle_swap _ _ B (@bone _ _ B) U (@bopp _ _ B (@bone _ _ B))). }
  apply (@bae_trans _ _ B _ (@bplus _ _ B (@bzero _ _ B) U) _).
  { apply (@bplus_wd_l _ _ B (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B))) (@bzero _ _ B) U
             (@bplus_opp _ _ B (@bone _ _ B))). }
  exact (@bplus_zero_l _ _ B U).
Qed.

(* ============================================================ *)
(* 5. Norm tail bounds (NormConv plus tail control)              *)
(* ============================================================ *)

Lemma bxcd_bsum_norm_le : forall (BA : Set) (bae : BA -> BA -> Set)
                                 (B : BanachAlg BA bae) (x : nat -> BA) (n : nat),
  QleT' (@bnorm _ _ B (bsum _ _ B (Datatypes.S n) x))
        (ncv_qsum (fun k : nat => @bnorm _ _ B (x k)) (Datatypes.S n)).
Proof.
  intros BA bae B x n. induction n as [| m IH].
  - change (bsum _ _ B (Datatypes.S 0%nat) x)
      with (@bplus _ _ B (@bzero _ _ B) (x 0%nat)).
    change (ncv_qsum (fun k : nat => @bnorm _ _ B (x k)) (Datatypes.S 0%nat))
      with (ncv_qsum (fun k : nat => @bnorm _ _ B (x k)) 0%nat
            + @bnorm _ _ B (x 0%nat))%Q.
    change (ncv_qsum (fun k : nat => @bnorm _ _ B (x k)) 0%nat) with 0%Q.
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _
               (@bnorm_wd _ _ B (@bplus _ _ B (@bzero _ _ B) (x 0%nat)) (x 0%nat)
                  (@bplus_zero_l _ _ B (x 0%nat))))).
    apply qeq_leT'. apply qeq_imp_qeqT. apply Qeq_sym. apply Qplus_0_l.
  - change (bsum _ _ B (Datatypes.S (Datatypes.S m)) x)
      with (@bplus _ _ B (bsum _ _ B (Datatypes.S m) x) (x (Datatypes.S m))).
    change (ncv_qsum (fun k => @bnorm _ _ B (x k)) (Datatypes.S (Datatypes.S m)))
      with (ncv_qsum (fun k => @bnorm _ _ B (x k)) (Datatypes.S m)
            + @bnorm _ _ B (x (Datatypes.S m)))%Q.
    eapply qleT'_trans.
    + exact (@bnorm_plus _ _ B (bsum _ _ B (Datatypes.S m) x) (x (Datatypes.S m))).
    + apply (qleT'_plus_compat _ _ _ _).
      * exact IH.
      * apply qleT'_refl.
Qed.

Lemma bxcd_F_norm_le : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (a : BA) (c : Q),
  Id c (@bnorm _ _ B a) ->
  forall j : nat, QleT' (@bnorm _ _ B (bxcd_F _ _ B a j)) (bxcd_A c j).
Proof.
  intros BA bae B a c Hc j. unfold bxcd_F, bxcd_A.
  apply Qle_to_QleT'.
  eapply Qle_trans.
  - exact (QleT'_to_Qle _ _
            (@bnorm_mult _ _ B (bpow _ _ B a j) (@bcoef _ _ B (/ q_fact j)))).
  - rewrite (qeqT_imp_qeq _ _ (@bnorm_coef_qeq _ _ B (/ q_fact j))).
    apply (Qle_trans _ ((q_pow (@bnorm _ _ B a) j) * Qabs (/ q_fact j))%Q).
    + apply (Qmult_le_compat_r (@bnorm _ _ B (bpow _ _ B a j))
                               (q_pow (@bnorm _ _ B a) j) (Qabs (/ q_fact j))).
      * apply QleT'_to_Qle. exact (@bnorm_bpow _ _ B a j).
      * rewrite (Qabs_pos (/ q_fact j)
                   (Qlt_le_weak 0 (/ q_fact j)
                      (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (q_fact_pos j))))).
        apply Qlt_le_weak. exact (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (q_fact_pos j))).
    + rewrite <- (id_eq_inv Hc).
      rewrite (Qabs_pos (/ q_fact j)
                 (Qlt_le_weak 0 (/ q_fact j)
                    (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (q_fact_pos j))))).
      apply Qle_refl.
Qed.

Lemma bxcd_G_norm_le : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (a : BA) (c : Q),
  Id c (@bnorm _ _ B a) ->
  forall i : nat, QleT' (@bnorm _ _ B (bxcd_G _ _ B a i)) (bxcd_A c i).
Proof.
  intros BA bae B a c Hc i. unfold bxcd_G, bxcd_A.
  apply Qle_to_QleT'.
  eapply Qle_trans.
  - exact (QleT'_to_Qle _ _
            (@bnorm_mult _ _ B (bpow _ _ B (@bopp _ _ B a) i) (@bcoef _ _ B (/ q_fact i)))).
  - rewrite (qeqT_imp_qeq _ _ (@bnorm_coef_qeq _ _ B (/ q_fact i))).
    apply (Qle_trans _ ((q_pow (@bnorm _ _ B a) i) * Qabs (/ q_fact i))%Q).
    + apply (Qmult_le_compat_r (@bnorm _ _ B (bpow _ _ B (@bopp _ _ B a) i))
                               (q_pow (@bnorm _ _ B a) i) (Qabs (/ q_fact i))).
      * apply QleT'_to_Qle.
        apply (qleT'_trans _ (q_pow (@bnorm _ _ B (@bopp _ _ B a)) i)%Q _).
        -- exact (@bnorm_bpow _ _ B (@bopp _ _ B a) i).
        -- rewrite <- (id_eq_inv (@bnorm_opp _ _ B a)). apply qleT'_refl.
      * rewrite (Qabs_pos (/ q_fact i)
                   (Qlt_le_weak 0 (/ q_fact i)
                      (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (q_fact_pos i))))).
        apply Qlt_le_weak. exact (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (q_fact_pos i))).
    + rewrite <- (id_eq_inv Hc).
      rewrite (Qabs_pos (/ q_fact i)
                 (Qlt_le_weak 0 (/ q_fact i)
                    (Qinv_lt_0_compat _ (QltT_to_Qlt _ _ (q_fact_pos i))))).
      apply Qle_refl.
Qed.

(* Four-argument multiplication monotonicity (all arguments
   nonneg-restricted; the stdlib has no bare Qmult_le_compat) *)
Lemma bxcd_Qmult_le_compat_nonneg : forall u v w x : Q,
  QleT' u v -> QleT' w x -> QleT' 0 w -> QleT' 0 v ->
  QleT' (u * w) (v * x).
Proof.
  intros u v w x Huv Hwx Hw Hv.
  apply Qle_to_QleT'.
  pose proof (QleT'_to_Qle _ _ Huv) as Huvp.
  pose proof (QleT'_to_Qle _ _ Hwx) as Hwxp.
  pose proof (QleT'_to_Qle _ _ Hw) as Hwp.
  pose proof (QleT'_to_Qle _ _ Hv) as Hvp.
  apply (Qle_trans _ (v * w)%Q).
  - exact (Qmult_le_compat_r u v w Huvp Hwp).
  - rewrite (Qmult_comm v w).
    apply (Qle_trans _ (x * v)%Q).
    + exact (Qmult_le_compat_r w x v Hwxp Hvp).
    + rewrite (Qmult_comm x v). apply Qle_refl.
Qed.

Lemma bxcd_Qmult_le_compat_l : forall u v w : Q,
  QleT' 0 w -> QleT' u v -> QleT' (w * u) (w * v).
Proof.
  intros u v w Hw Huv.
  apply Qle_to_QleT'.
  rewrite (Qmult_comm w u), (Qmult_comm w v).
  exact (Qmult_le_compat_r u v w (QleT'_to_Qle _ _ Huv) (QleT'_to_Qle _ _ Hw)).
Qed.

Lemma bxcd_A_ge0 : forall (c : Q), QleT' 0 c -> forall i : nat, QleT' 0 (bxcd_A c i).
Proof.
  intros c Hc i. unfold bxcd_A.
  apply Qle_to_QleT'.
  apply (Qle_trans _ (((q_pow c i / q_fact i) * (1 + 1)%Q) * / (1 + 1)%Q)%Q).
  - assert (Hm : QleT' (0 * 0)%Q
                   (((q_pow c i / q_fact i) * (1 + 1)%Q) * / (1 + 1)%Q)%Q)
      by (apply bxcd_Qmult_le_compat_nonneg;
            [ exact (q_pow_fact2_nonneg c i Hc)
            | (apply Qle_to_QleT'; apply Qlt_le_weak;
               change (1+1)%Q with (q_fact 2%nat);
               apply Qinv_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos)
            | apply qleT'_refl
            | exact (q_pow_fact2_nonneg c i Hc) ]).
    apply QleT'_to_Qle in Hm. rewrite Qmult_0_l in Hm. exact Hm.
  - assert (Hf : (((q_pow c i / q_fact i) * (1 + 1)%Q) * / (1 + 1)%Q)
                 == (q_pow c i / q_fact i)).
    { field. intro Hden.
      exact (Qlt_not_eq 0 (q_fact i) (QltT_to_Qlt _ _ (q_fact_pos i))
               (Qeq_sym _ _ Hden)). }
    rewrite Hf. apply Qle_refl.
Qed.


Lemma bxcd_term_norm : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (a : BA) (c : Q),
  Id c (@bnorm _ _ B a) ->
  forall j i : nat,
    QleT' (@bnorm _ _ B (@bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)))
        ((bxcd_A c j * bxcd_A c i)%Q).
Proof.
  intros BA bae B a c Hc j i.
  assert (Hc0 : QleT' 0 c).
  { rewrite (id_eq_inv Hc). exact (@bnorm_pos _ _ B a). }
  eapply qleT'_trans.
  - exact (@bnorm_mult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)).
  - apply bxcd_Qmult_le_compat_nonneg.
    + exact (bxcd_F_norm_le _ _ B a c Hc j).
    + exact (bxcd_G_norm_le _ _ B a c Hc i).
    + exact (@bnorm_pos _ _ B (bxcd_G _ _ B a i)).
    + apply bxcd_A_ge0. exact Hc0.
Qed.

Lemma bxcd_qtail_ge0 : forall (c : Q), QleT' 0 c ->
  forall m n : nat, QleT' 0 (exp_tail_abs m n c).
Proof.
  intros c Hc m. induction n as [| n' IH].
  - apply qleT'_refl.
  - change (exp_tail_abs m (Datatypes.S n') c)
      with ((exp_tail_abs m n' c
             + (if Nat.leb m n'
                then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                else 0%Q))%Q).
    destruct (Nat.leb m n').
    + apply Qle_to_QleT'.
      exact (Qplus_le_compat 0 (exp_tail_abs m n' c) 0
               (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))
               (QleT'_to_Qle _ _ IH)
               (QleT'_to_Qle _ _ (bxcd_A_ge0 c Hc (Datatypes.S n')))).
    + apply Qle_to_QleT'.
      rewrite (Qplus_0_r (exp_tail_abs m n' c)).
      exact (QleT'_to_Qle _ _ IH).
Qed.

Lemma bxcd_qtail_add : forall (c : Q) (m p n : nat),
  NatLe m p -> NatLe p n ->
  QeqT (exp_tail_abs m n c) (exp_tail_abs m p c + exp_tail_abs p n c)%Q.
Proof.
  intros c m p n Hmp Hpn.
  pose proof (NatLe_drop _ _ Hmp) as Hmpp.
  revert Hpn. induction n as [| n' IH]; intros Hpn.
  - pose proof (NatLe_drop _ _ Hpn) as Hpnp.
    assert (Hp0 : p = 0%nat) by lia. subst p.
    apply qeq_imp_qeqT.
    change (exp_tail_abs 0%nat 0%nat c) with 0%Q.
    ring.
  - pose proof (NatLe_drop _ _ Hpn) as Hpnp.
    apply qeq_imp_qeqT.
    destruct (Nat.eq_dec p (Datatypes.S n')) as [Heq | Hne].
    + subst p.
      rewrite (qeqT_imp_qeq _ _
                 (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n') c (Nat.le_refl _))).
      ring.
    + assert (Hpn' : (p <= n')%nat) by lia.
      change (exp_tail_abs m (Datatypes.S n') c)
        with ((exp_tail_abs m n' c
               + (if Nat.leb m n'
                  then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                  else 0%Q))%Q).
      change (exp_tail_abs p (Datatypes.S n') c)
        with ((exp_tail_abs p n' c
               + (if Nat.leb p n'
                  then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                  else 0%Q))%Q).
      assert (Hm1 : Nat.leb m n' = true) by (apply Nat.leb_le; lia).
      assert (Hp1 : Nat.leb p n' = true) by (apply Nat.leb_le; lia).
      assert (HpN : NatLe p n') by (apply NatLe_lift; lia).
      rewrite Hm1, Hp1, (qeqT_imp_qeq _ _ (IH HpN)). ring.
Qed.

Lemma bxcd_qtail_mono : forall (c : Q), QleT' 0 c -> forall (k1 k2 n : nat),
  NatLe k1 k2 -> NatLe k2 n ->
  QleT' (exp_tail_abs k2 n c) (exp_tail_abs k1 n c).
Proof.
  intros c Hc0 k1 k2 n H12 H2n.
  pose proof (NatLe_drop _ _ H12) as H12p.
  pose proof (NatLe_drop _ _ H2n) as H2np.
  apply Qle_to_QleT'.
  rewrite (qeqT_imp_qeq _ _ (bxcd_qtail_add c k1 k2 n H12 H2n)).
  assert (Hg : Qle 0 (exp_tail_abs k1 k2 c))
    by (apply QleT'_to_Qle; apply bxcd_qtail_ge0; exact Hc0).
  assert (Hz : Qle (exp_tail_abs k2 n c + 0%Q)
                   (exp_tail_abs k2 n c + exp_tail_abs k1 k2 c))
    by (apply Qplus_le_compat; [apply Qle_refl | exact Hg]).
  rewrite (Qplus_0_r (exp_tail_abs k2 n c)) in Hz.
  rewrite (Qplus_comm (exp_tail_abs k2 n c) (exp_tail_abs k1 k2 c)) in Hz.
  exact Hz.
Qed.

Lemma bxcd_qsum_plus : forall (f g : nat -> Q) (n : nat),
  QeqT (ncv_qsum (fun k : nat => (f k + g k)%Q) n)
       ((ncv_qsum f n + ncv_qsum g n)%Q).
Proof.
  intros f g n. induction n as [| m IH]; apply qeq_imp_qeqT.
  - reflexivity.
  - change (ncv_qsum (fun k : nat => (f k + g k)%Q) (Datatypes.S m))
      with ((ncv_qsum (fun k : nat => (f k + g k)%Q) m + (f m + g m)%Q)%Q).
    change (ncv_qsum f (Datatypes.S m)) with ((ncv_qsum f m + f m)%Q).
    change (ncv_qsum g (Datatypes.S m)) with ((ncv_qsum g m + g m)%Q).
    rewrite (qeqT_imp_qeq _ _ IH). ring.
Qed.

Lemma bxcd_qsum_scalar_r : forall (f : nat -> Q) (c : Q) (n : nat),
  QeqT (ncv_qsum (fun k : nat => (f k * c)%Q) n) ((ncv_qsum f n * c)%Q).
Proof.
  intros f c n. induction n as [| m IH]; apply qeq_imp_qeqT.
  - reflexivity.
  - change (ncv_qsum (fun k : nat => (f k * c)%Q) (Datatypes.S m))
      with ((ncv_qsum (fun k : nat => (f k * c)%Q) m + (f m * c)%Q)%Q).
    change (ncv_qsum f (Datatypes.S m)) with ((ncv_qsum f m + f m)%Q).
    rewrite (qeqT_imp_qeq _ _ IH). ring.
Qed.

Lemma bxcd_qsum_head_shift : forall (c : Q) (k : nat),
  QeqT (ncv_qsum (fun i : nat => bxcd_A c (Datatypes.S i)) k)
       (exp_tail_abs 0%nat k c).
Proof.
  intros c k. induction k as [| m IH]; apply qeq_imp_qeqT.
  - reflexivity.
  - change (ncv_qsum (fun i : nat => bxcd_A c (Datatypes.S i)) (Datatypes.S m))
      with ((ncv_qsum (fun i : nat => bxcd_A c (Datatypes.S i)) m
             + bxcd_A c (Datatypes.S m))%Q).
    change (exp_tail_abs 0%nat (Datatypes.S m) c)
      with ((exp_tail_abs 0%nat m c
             + (if Nat.leb 0%nat m
                then (q_pow c (Datatypes.S m) / q_fact (Datatypes.S m))%Q
                else 0%Q))%Q).
    assert (Hl : Nat.leb 0%nat m = true) by (destruct m; reflexivity).
    rewrite Hl, (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.


Lemma bxcd_padsum_tail : forall (c b0 : Q) (t n : nat),
  QeqT (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
           (Datatypes.S n))
       ((b0 * exp_tail_abs t n c)%Q).
Proof.
  intros c b0 t n. induction n as [| n' IH]; apply qeq_imp_qeqT.
  - change (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
              (Datatypes.S 0%nat))
      with ((if Nat.ltb t 0%nat then (b0 * bxcd_A c 0%nat)%Q else 0%Q)%Q).
    change (exp_tail_abs t 0%nat c) with 0%Q.
    assert (H0 : Nat.ltb t 0%nat = false) by reflexivity.
    rewrite H0.
    change (if false then (b0 * bxcd_A c 0%nat)%Q else 0%Q) with 0%Q.
    ring.
  - change (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
              (Datatypes.S (Datatypes.S n')))
      with ((ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q)
             (Datatypes.S n')
             + (if Nat.ltb t (Datatypes.S n')
                then (b0 * bxcd_A c (Datatypes.S n'))%Q
                else 0%Q))%Q).
    change (exp_tail_abs t (Datatypes.S n') c)
      with ((exp_tail_abs t n' c
             + (if Nat.leb t n'
                then (q_pow c (Datatypes.S n') / q_fact (Datatypes.S n'))%Q
                else 0%Q))%Q).
    rewrite (qeqT_imp_qeq _ _ IH).
    assert (Hg : Nat.ltb t (Datatypes.S n') = Nat.leb t n') by reflexivity.
    rewrite Hg.
    unfold bxcd_A. destruct (Nat.leb t n'); ring.
Qed.

Lemma bxcd_row_le : forall (c b0 : Q) (t n : nat),
  NatLe t n -> QleT' 0 b0 -> QleT' 0 c ->
  QleT' (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) n)
        (b0 * exp_tail_abs t n c).
Proof.
  intros c b0 t n Htn Hb0 Hc0.
  pose proof (NatLe_drop _ _ Htn) as Htnp.
  apply Qle_to_QleT'.
  assert (Hfn : Qle 0 (if Nat.ltb t n then (b0 * bxcd_A c n)%Q else 0%Q)).
  { destruct (Nat.ltb t n).
    - exact (QleT'_to_Qle _ _
               (@bxcd_Qmult_le_compat_nonneg 0%Q b0%Q 0%Q (bxcd_A c n)
                  Hb0 (bxcd_A_ge0 c Hc0 n) (qleT'_refl 0%Q) Hb0)).
    - apply Qle_refl. }
  assert (Hstep : Qle (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) n)
                      (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))).
  { rewrite <- (Qplus_0_r (ncv_qsum (fun i : nat => if Nat.ltb t i then (b0 * bxcd_A c i)%Q else 0%Q) n)).
    apply Qplus_le_compat; [apply Qle_refl | exact Hfn]. }
  eapply Qle_trans. exact Hstep.
  rewrite (qeqT_imp_qeq _ _ (bxcd_padsum_tail c b0 t n)). apply Qle_refl.
Qed.

Lemma bxcd_U_norm_le : forall (BA : Set) (bae : BA -> BA -> Set)
                              (B : BanachAlg BA bae) (a : BA) (c : Q) (n : nat),
  Id c (@bnorm _ _ B a) ->
  QleT' (@bnorm _ _ B (bxcd_U _ _ B a n))
        (ncv_qsum (fun j : nat =>
            ncv_qsum (fun i : nat =>
               if Nat.ltb (Nat.sub n j) i
               then (bxcd_A c j * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))
           (Datatypes.S n)).
Proof.
  intros BA bae B a c n Hc. unfold bxcd_U.
  eapply qleT'_trans.
  { apply (bxcd_bsum_norm_le _ _ B
              (fun j : nat => bsum _ _ B (Datatypes.S n)
                 (fun i : nat =>
                    if Nat.ltb (Nat.sub n j) i
                    then @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)
                    else @bzero _ _ B)) n). }
  apply ncv_qsum_le. intros j.
  eapply qleT'_trans.
  { apply (bxcd_bsum_norm_le _ _ B
              (fun i : nat =>
                 if Nat.ltb (Nat.sub n j) i
                 then @bmult _ _ B (bxcd_F _ _ B a j) (bxcd_G _ _ B a i)
                 else @bzero _ _ B) n). }
  apply ncv_qsum_le. intros i.
  destruct (Nat.ltb (Nat.sub n j) i).
  - exact (bxcd_term_norm _ _ B a c Hc j i).
  - rewrite <- (id_eq_inv (@bnorm_zero _ _ B)). apply qleT'_refl.
Qed.

(* Q2 <= E tail + E tail (the main tail-control item) *)
Lemma bxcd_Q2_bound : forall (c : Q) (K n : nat) (E : Q),
  QleT' 0 c ->
  (forall u : nat, NatLe K u -> QleT' ((1 + 1)%Q * c) (Z.of_nat (u + 1) # 1)) ->
  QleT' 0 E ->
  QleT' (exp_tail_abs 0%nat K c + bxcd_A c K * (1 + 1)%Q) E ->
  (forall m : nat, QleT' (ncv_qsum (fun i : nat => bxcd_A c i) m) E) ->
  NatLe (2 * K) n ->
  QleT' (ncv_qsum (fun j : nat =>
          ncv_qsum (fun i : nat =>
             if Nat.ltb (Nat.sub n j) i
             then (bxcd_A c j * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))
         (Datatypes.S n))
      ((E * exp_tail_abs K n c
        + E * exp_tail_abs K n c)%Q).
Proof.
  intros c K n E Hc0 Harch HEpos HE2 HE Hk2.
  pose proof (NatLe_drop _ _ Hk2) as Hk2p.
  pose proof (QleT'_to_Qle _ _ Hc0) as Hc0p.
  assert (Harchp : forall u : nat, (K <= u)%nat ->
            Qle ((1 + 1)%Q * c) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply Harch. apply NatLe_lift. exact Hu. }
  pose proof (QleT'_to_Qle _ _ HEpos) as HEposp.
  pose proof (QleT'_to_Qle _ _ HE2) as HE2p.
  assert (HEp : forall m : nat, Qle (ncv_qsum (fun i : nat => bxcd_A c i) m) E)
    by (intros m; apply QleT'_to_Qle; apply HE).
  apply Qle_to_QleT'.
  assert (Hkn : (K <= n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (Hkn2 : (2 * K <= n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  apply (Qle_trans _
    (ncv_qsum (fun j : nat =>
        (bxcd_A c j * exp_tail_abs (K) n c
         + (if Nat.ltb (K) j then (E * bxcd_A c j)%Q else 0%Q))%Q)
        (Datatypes.S n))).
  - apply QleT'_to_Qle. apply ncv_qsum_le. intros j. apply Qle_to_QleT'.
    eapply Qle_trans.
    + rewrite (qeqT_imp_qeq _ _
                 (bxcd_padsum_tail c (bxcd_A c j) (Nat.sub n j) n)).
      apply Qle_refl.
    + destruct (Nat.ltb (K) j) eqn:Ekj.
      * (* K < j: A_j tail(n-j) <= A_j tail(0,n) = A_j (tail0K+tailKn)
           <= A_j (tailKn+E) = the right-hand side *)
        assert (Htle : Qle (exp_tail_abs 0%nat K c)
                         (exp_tail_abs K n c + E)%Q).
        { apply (Qle_trans _ (exp_tail_abs 0%nat K c
                             + bxcd_A c K * (1 + 1)%Q)%Q).
          - assert (Haug : Qle (exp_tail_abs 0%nat K c + 0%Q)
                          (exp_tail_abs 0%nat K c + bxcd_A c K * (1 + 1)%Q)%Q)
                  by (apply Qplus_le_compat; [apply Qle_refl
                                             | apply QleT'_to_Qle;
                                               apply (qleT'_mult_compat_r
                                                        0%Q (bxcd_A c K) (1 + 1)%Q);
                                               [apply Q2_nonneg
                                               | apply bxcd_A_ge0; exact Hc0]]).
            rewrite (Qplus_0_r (exp_tail_abs 0%nat K c)) in Haug.
            exact Haug.
          - apply (Qle_trans _ E).
            ++ exact HE2p.
            ++ assert (Hzero : Qle 0 (exp_tail_abs K n c))
                 by (apply QleT'_to_Qle; apply bxcd_qtail_ge0; exact Hc0).
               assert (Hr : Qle E (E + exp_tail_abs K n c))
                 by exact (Qle_plus_nonneg_r E (exp_tail_abs K n c) Hzero).
               rewrite (Qplus_comm E (exp_tail_abs K n c)) in Hr.
               exact Hr. }
        eapply (Qle_trans _ (bxcd_A c j * exp_tail_abs 0%nat n c)%Q).
        -- apply QleT'_to_Qle.
           exact (@bxcd_Qmult_le_compat_l
                    (exp_tail_abs (Nat.sub n j) n c)
                    (exp_tail_abs 0%nat n c) (bxcd_A c j)
                    (bxcd_A_ge0 c Hc0 j)
                    (bxcd_qtail_mono c Hc0 0%nat (Nat.sub n j) n
                       ltac:(apply NatLe_lift; lia) ltac:(apply NatLe_lift; lia))).
        -- eapply (Qle_trans _ (bxcd_A c j
                   * (exp_tail_abs 0%nat K c + exp_tail_abs K n c))%Q).
           ++ rewrite (qeqT_imp_qeq _ _
                        (bxcd_qtail_add c 0%nat K n
                           ltac:(apply NatLe_lift; lia)
                           ltac:(apply NatLe_lift; lia))).
              apply (Qle_refl _).
           ++ assert (HT0 : Qle (exp_tail_abs 0%nat K c) E).
              { apply (Qle_trans _ (exp_tail_abs 0%nat K c
                                   + bxcd_A c K * (1 + 1)%Q)%Q).
                - assert (Hz : Qle (exp_tail_abs 0%nat K c + 0%Q)
                              (exp_tail_abs 0%nat K c
                               + bxcd_A c K * (1 + 1)%Q)%Q).
                  { apply Qplus_le_compat; [apply Qle_refl
                                           | apply QleT'_to_Qle].
                    apply (qleT'_mult_compat_r
                             0%Q (bxcd_A c K) (1 + 1)%Q).
                    ++ apply Q2_nonneg.
                    ++ apply bxcd_A_ge0; exact Hc0. }
                  rewrite (Qplus_0_r (exp_tail_abs 0%nat K c)) in Hz.
                  exact Hz.
                - exact HE2p. }
              assert (Hsum : Qle (exp_tail_abs 0%nat K c + exp_tail_abs K n c)
                                (exp_tail_abs K n c + E)%Q).
              { apply (Qle_trans _ (E + exp_tail_abs K n c)%Q).
                - apply Qplus_le_compat; [exact HT0 | apply Qle_refl].
                - rewrite (Qplus_comm E (exp_tail_abs K n c)).
                  apply Qle_refl. }
              rewrite (Qmult_comm E (bxcd_A c j)).
              rewrite <- (Qmult_plus_distr_r (bxcd_A c j)
                            (exp_tail_abs K n c) E).
              apply QleT'_to_Qle.
              exact (@bxcd_Qmult_le_compat_l
                       (exp_tail_abs 0%nat K c + exp_tail_abs K n c)%Q
                       (exp_tail_abs K n c + E)%Q (bxcd_A c j)
                       (bxcd_A_ge0 c Hc0 j) (Qle_to_QleT' _ _ Hsum)).
      * (* j <= K: tail(n-j) <= tail(K) *)
        apply Nat.ltb_ge in Ekj.
        eapply (Qle_trans _ (bxcd_A c j * exp_tail_abs (K) n c)%Q).
        -- apply QleT'_to_Qle.
           exact (bxcd_Qmult_le_compat_l _ _ (bxcd_A c j)
                    (bxcd_A_ge0 c Hc0 j)
                    (bxcd_qtail_mono c Hc0 (K) (Nat.sub n j) n
                       ltac:(apply NatLe_lift; lia) ltac:(apply NatLe_lift; lia))).
        -- exact (Qle_plus_nonneg_r (bxcd_A c j * exp_tail_abs (K) n c) 0%Q
                    (Qle_refl 0%Q)).
  - assert (Hsplit := qeqT_imp_qeq _ _ (bxcd_qsum_plus
               (fun j : nat => bxcd_A c j * exp_tail_abs (K) n c)
               (fun j : nat =>
                  if Nat.ltb (K) j then (E * bxcd_A c j)%Q else 0%Q)
               (Datatypes.S n))).
    rewrite Hsplit.
    apply Qplus_le_compat.
    + rewrite (qeqT_imp_qeq _ _
                 (bxcd_qsum_scalar_r (fun j : nat => bxcd_A c j)
                    (exp_tail_abs (K) n c) (Datatypes.S n))).
      exact (Qmult_le_compat_r
               (ncv_qsum (fun i : nat => bxcd_A c i) (Datatypes.S n)) E
               (exp_tail_abs (K) n c)
               (HEp (Datatypes.S n))
               (QleT'_to_Qle _ _ (bxcd_qtail_ge0 c Hc0 (K) n))).
    + rewrite (qeqT_imp_qeq _ _ (bxcd_padsum_tail c E (K) n)). apply Qle_refl.
Qed.

(* CD12: the endgame wants the div2 n tail-segment shape. The K-shape
   bound (bxcd_Q2_bound) pins the tail-segment start at K and does not
   shrink with n, while the endgame chain (Htl = tail(div2 n,n) < q/D
   plus bxcd_q_div_lt r := 2E < D) must mathematically be bounded by a
   tail segment shrinking with n. Split rows at M = div2 n:
   rows j <= M are monotone (n-j >= n-M >= M); rows j > M split the
   segment by qtail_add, giving tail(n-j,M) <= tail(0,M) <= E
   (tail(0,M) = tail(0,K) + tail(K,M) <= (E - A_K 2) + A_K 2 = HE2).
   The aggregation is isomorphic to the K shape. *)
Lemma bxcd_Q2_bound_M : forall (c : Q) (K n : nat) (E : Q),
  QleT' 0 c ->
  (forall u : nat, NatLe K u -> QleT' ((1 + 1)%Q * c) (Z.of_nat (u + 1) # 1)) ->
  QleT' 0 E ->
  QleT' (exp_tail_abs 0%nat K c + bxcd_A c K * (1 + 1)%Q) E ->
  (forall m : nat, QleT' (ncv_qsum (fun i : nat => bxcd_A c i) m) E) ->
  NatLe (2 * K) n ->
  QleT' (ncv_qsum (fun j : nat =>
          ncv_qsum (fun i : nat =>
             if Nat.ltb (Nat.sub n j) i
             then (bxcd_A c j * bxcd_A c i)%Q else 0%Q) (Datatypes.S n))
         (Datatypes.S n))
      ((E * exp_tail_abs (Nat.div2 n) n c
        + E * exp_tail_abs (Nat.div2 n) n c)%Q).
Proof.
  intros c K n E Hc0 Harch HEpos HE2 HE Hk2.
  pose proof (NatLe_drop _ _ Hk2) as Hk2p.
  pose proof (QleT'_to_Qle _ _ Hc0) as Hc0p.
  assert (Harchp : forall u : nat, (K <= u)%nat ->
            Qle ((1 + 1)%Q * c) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply Harch. apply NatLe_lift. exact Hu. }
  pose proof (QleT'_to_Qle _ _ HEpos) as HEposp.
  pose proof (QleT'_to_Qle _ _ HE2) as HE2p.
  assert (HEp : forall m : nat, Qle (ncv_qsum (fun i : nat => bxcd_A c i) m) E)
    by (intros m; apply QleT'_to_Qle; apply HE).
  apply Qle_to_QleT'.
  assert (H2M : (2 * Nat.div2 n <= n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (HKM : (K <= Nat.div2 n)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (Hdbound : (n <= 2 * Nat.div2 n + 1)%nat).
  { pose proof (Nat.div2_odd n) as Hd. destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia. }
  assert (Ht0M : Qle (exp_tail_abs 0%nat (Nat.div2 n) c) E).
  { rewrite (qeqT_imp_qeq _ _
               (bxcd_qtail_add c 0%nat K (Nat.div2 n)
                  ltac:(apply NatLe_lift; lia) ltac:(apply NatLe_lift; exact HKM))).
    apply (Qle_trans _ (exp_tail_abs 0%nat K c
                       + bxcd_A c K * (1 + 1)%Q)%Q).
    - apply Qplus_le_compat; [apply Qle_refl | ].
      exact (QleT'_to_Qle _ _
               (exp_tail_abs_geom2 c K (Nat.div2 n) Hc0 Harch HKM)).
    - exact HE2p. }
  apply (Qle_trans _
    (ncv_qsum (fun j : nat =>
        (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c
         + (if Nat.ltb (Nat.div2 n) j then (E * bxcd_A c j)%Q else 0%Q))%Q)
        (Datatypes.S n))).
  - apply QleT'_to_Qle. apply ncv_qsum_le. intros j. apply Qle_to_QleT'.
    eapply Qle_trans.
    + rewrite (qeqT_imp_qeq _ _
                 (bxcd_padsum_tail c (bxcd_A c j) (Nat.sub n j) n)).
      apply Qle_refl.
    + destruct (Nat.ltb (Nat.div2 n) j) eqn:EMj.
      * (* div2 n < j: tail(n-j,n) = tail(n-j,M) + tail(M,n),
           tail(n-j,M) <= tail(0,M) <= E *)
        apply Nat.ltb_lt in EMj.
        assert (HnjM : (Nat.sub n j <= Nat.div2 n)%nat) by lia.
        assert (Ht1T : QleT' (exp_tail_abs (Nat.sub n j) (Nat.div2 n) c) E).
        { apply Qle_to_QleT'.
          apply (Qle_trans _ (exp_tail_abs 0%nat (Nat.div2 n) c)).
          - exact (QleT'_to_Qle _ _
                     (bxcd_qtail_mono c Hc0 0%nat (Nat.sub n j) (Nat.div2 n)
                        ltac:(apply NatLe_lift; lia)
                        ltac:(apply NatLe_lift; exact HnjM))).
          - exact Ht0M. }
        rewrite (qeqT_imp_qeq _ _
                   (bxcd_qtail_add c (Nat.sub n j) (Nat.div2 n) n
                      (NatLe_lift _ _ HnjM) ltac:(apply NatLe_lift; lia))).
        rewrite (Qmult_plus_distr_r (bxcd_A c j)
                   (exp_tail_abs (Nat.sub n j) (Nat.div2 n) c)
                   (exp_tail_abs (Nat.div2 n) n c)).
        rewrite (Qplus_comm (bxcd_A c j * exp_tail_abs (Nat.sub n j) (Nat.div2 n) c)
                            (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c)).
        apply Qplus_le_compat; [apply Qle_refl | ].
        rewrite (Qmult_comm E (bxcd_A c j)).
        exact (QleT'_to_Qle _ _
                 (bxcd_Qmult_le_compat_l (exp_tail_abs (Nat.sub n j) (Nat.div2 n) c)
                    E (bxcd_A c j) (bxcd_A_ge0 c Hc0 j) Ht1T)).
      * (* j <= div2 n: tail(n-j,n) <= tail(div2 n,n) *)
        apply Nat.ltb_ge in EMj.
        eapply (Qle_trans _ (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c)%Q).
        -- apply QleT'_to_Qle.
           exact (bxcd_Qmult_le_compat_l _ _ (bxcd_A c j)
                    (bxcd_A_ge0 c Hc0 j)
                    (bxcd_qtail_mono c Hc0 (Nat.div2 n) (Nat.sub n j) n
                       ltac:(apply NatLe_lift; lia) ltac:(apply NatLe_lift; lia))).
        -- exact (Qle_plus_nonneg_r
                    (bxcd_A c j * exp_tail_abs (Nat.div2 n) n c) 0%Q
                    (Qle_refl 0%Q)).
  - assert (Hsplit := qeqT_imp_qeq _ _ (bxcd_qsum_plus
               (fun j : nat => bxcd_A c j * exp_tail_abs (Nat.div2 n) n c)
               (fun j : nat =>
                  if Nat.ltb (Nat.div2 n) j then (E * bxcd_A c j)%Q else 0%Q)
               (Datatypes.S n))).
    rewrite Hsplit.
    apply Qplus_le_compat.
    + rewrite (qeqT_imp_qeq _ _
                 (bxcd_qsum_scalar_r (fun j : nat => bxcd_A c j)
                    (exp_tail_abs (Nat.div2 n) n c) (Datatypes.S n))).
      exact (Qmult_le_compat_r
               (ncv_qsum (fun i : nat => bxcd_A c i) (Datatypes.S n)) E
               (exp_tail_abs (Nat.div2 n) n c)
               (HEp (Datatypes.S n))
               (QleT'_to_Qle _ _ (bxcd_qtail_ge0 c Hc0 (Nat.div2 n) n))).
    + rewrite (qeqT_imp_qeq _ _
                 (bxcd_padsum_tail c E (Nat.div2 n) n)). apply Qle_refl.
Qed.

(* ============================================================ *)
(* 6. The fallback main item: the partial-sum product is         *)
(*    epsilon-close to 1                                         *)
(* ============================================================ *)


Lemma bxcd_q_div_lt : forall r D q : Q,
  QltT 0 q -> QleT' 0 r -> QltT r D -> QltT 0 D -> QltT (r * (q * / D)) q.
Proof.
  intros r D q Hq Hr HD' HD.
  apply Qlt_to_QltT.
  pose proof (QltT_to_Qlt _ _ Hq) as Hqp.
  pose proof (QleT'_to_Qle _ _ Hr) as Hrp.
  pose proof (QltT_to_Qlt _ _ HD') as HD'p.
  pose proof (QltT_to_Qlt _ _ HD) as HDp.
  apply (Qlt_le_trans _ (D * (q * / D))%Q).
  - apply (Qmult_lt_compat_r).
    + apply QltT_to_Qlt. apply ncv_qmult_lt0.
      * exact Hqp.
      * apply Qinv_lt_0_compat. exact HDp.
    + exact HD'p.
  - assert (Hdd : (D * (q * / D))%Q == q)
      by (field; intro Hden;
            exact (Qlt_not_eq 0 D (QltT_to_Qlt _ _ HD) (Qeq_sym _ _ Hden))).
    rewrite Hdd. apply Qle_refl.
Qed.

(* The fallback main item: for every q > 0 there is an explicitly
   computed bound N such that for all n >= N the norm of
   (partial exp a)(n) * (partial exp -a)(n) - 1 is below q. *)
Theorem bxcd_prod_near_one : forall (BA : Set) (bae : BA -> BA -> Set)
                                    (B : BanachAlg BA bae) (a : BA),
  forall q : Q, QltT 0 q ->
  sigT (fun N : nat => forall n : nat, NatLe N n ->
    QltT (@bnorm _ _ B (@bplus _ _ B (@bmult _ _ B (exp_series_partial _ _ B a n)
                                        (exp_series_partial _ _ B (@bopp _ _ B a) n))
                              (@bopp _ _ B (@bone _ _ B)))) q).
Proof.
  intros BA bae B a q Hq.
  assert (Hc0 : QleT' 0 (@bnorm _ _ B a)) by (apply (@bnorm_pos _ _ B a)).
  assert (H01T : QltT 0 1%Q).
  { pose proof (q_fact_pos 0%nat) as H. change (q_fact 0%nat) with 1%Q in H. exact H. }
  assert (H01 : Qlt 0 1%Q) by (apply QltT_to_Qlt; exact H01T).
  destruct (q_arch_geom (@bnorm _ _ B a)) as [K HK].
  assert (Harch : forall u : nat, NatLe K u ->
            QleT' ((1 + 1)%Q * (@bnorm _ _ B a)) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. exact (HK u Hu). }
  assert (HE2 : QleT' (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                      + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)
                    (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                          + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q).
  { apply Qle_to_QleT'.
    apply (Qle_trans _ (0 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                              + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q).
    - rewrite (Qplus_0_l (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                            + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)).
      apply Qle_refl.
    - apply (@Qplus_le_compat 0%Q 1%Q
                (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                 + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q
                (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                 + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q).
      ++ exact (Qlt_le_weak 0%Q 1%Q H01).
      ++ apply Qle_refl. }
  assert (HE : forall m : nat,
           QleT' (ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i) m)
               (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                     + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q).
  { intros m. apply Qle_to_QleT'. destruct m as [| m'].
    - apply (Qle_trans _ 1%Q).
      + exact (Qlt_le_weak 0%Q 1%Q H01).
      + assert (Hz3 : Qle 0 (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                           + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q).
        { assert (Hg3 : Qle 0 (bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)).
          { apply QleT'_to_Qle.
            apply (qleT'_mult_compat_r 0%Q (bxcd_A (@bnorm _ _ B a) K) (1 + 1)%Q).
            ++ apply Q2_nonneg.
            ++ apply bxcd_A_ge0; exact Hc0. }
          apply (@Qplus_le_compat 0%Q (exp_tail_abs 0%nat K (@bnorm _ _ B a))
                    0%Q (bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)).
          ++ apply QleT'_to_Qle. apply bxcd_qtail_ge0. exact Hc0.
          ++ exact Hg3. }
        exact (Qle_plus_nonneg_r 1%Q (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                     + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q Hz3).
    - assert (Hsplit : ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i)
                         (Datatypes.S m')
                       == (1 + ncv_qsum (fun i : nat =>
                             bxcd_A (@bnorm _ _ B a) (Datatypes.S i)) m')%Q).
      { induction m' as [| m'' IH2].
        - change (ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i)
                    (Datatypes.S 0%nat))
            with ((ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i) 0%nat
                   + bxcd_A (@bnorm _ _ B a) 0%nat)%Q).
          change (ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i) 0%nat) with 0%Q.
          unfold bxcd_A. change (q_pow (@bnorm _ _ B a) 0%nat) with 1%Q.
          change (q_fact 0%nat) with 1%Q. unfold Qdiv. simpl.
          change (ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm _ _ B a) (Datatypes.S i)) 0%nat) with 0%Q.
          change (1 + ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm _ _ B a) (Datatypes.S i)) 0%nat)%Q with 1%Q.
          reflexivity.
        - change (ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i)
                    (Datatypes.S (Datatypes.S m'')))
            with ((ncv_qsum (fun i : nat => bxcd_A (@bnorm _ _ B a) i)
                    (Datatypes.S m'') + bxcd_A (@bnorm _ _ B a) (Datatypes.S m''))%Q).
          change (ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm _ _ B a) (Datatypes.S i))
                   (Datatypes.S m''))%Q
            with (ncv_qsum (fun i : nat =>
                   bxcd_A (@bnorm _ _ B a) (Datatypes.S i)) m''
                  + bxcd_A (@bnorm _ _ B a) (Datatypes.S m''))%Q.
          rewrite IH2.
          rewrite (Qplus_assoc 1%Q
                     (ncv_qsum (fun i : nat =>
                        bxcd_A (@bnorm _ _ B a) (Datatypes.S i)) m'')
                     (bxcd_A (@bnorm _ _ B a) (Datatypes.S m''))).
          reflexivity. }
      rewrite Hsplit, (qeqT_imp_qeq _ _ (bxcd_qsum_head_shift (@bnorm _ _ B a) m')).
      destruct (Nat.leb_spec m' K) as [HmK | HmK].
      + (* case m' <= K: tail(0,m') <= tail(0,K) + A_K*2, split at m' *)
        apply Qplus_le_compat; [apply Qle_refl | ].
        assert (Hz : Qle 0 (exp_tail_abs m' K (@bnorm _ _ B a)
                            + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q).
        { apply (@Qplus_le_compat 0%Q (exp_tail_abs m' K (@bnorm _ _ B a))
                    0%Q (bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)).
          ++ apply QleT'_to_Qle. apply bxcd_qtail_ge0. exact Hc0.
          ++ apply QleT'_to_Qle.
             apply (qleT'_mult_compat_r 0%Q (bxcd_A (@bnorm _ _ B a) K) (1 + 1)%Q).
             ** apply Q2_nonneg.
             ** apply bxcd_A_ge0; exact Hc0. }
        rewrite (qeqT_imp_qeq _ _
                   (bxcd_qtail_add (@bnorm _ _ B a) 0%nat m' K
                      ltac:(apply NatLe_lift; lia)
                      ltac:(apply NatLe_lift; exact HmK))).
        apply (Qle_trans _
                 (exp_tail_abs 0%nat m' (@bnorm _ _ B a)
                  + (exp_tail_abs m' K (@bnorm _ _ B a)
                     + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q).
        * apply Qle_plus_nonneg_r. exact Hz.
        * rewrite (Qplus_assoc (exp_tail_abs 0%nat m' (@bnorm _ _ B a))
                    (exp_tail_abs m' K (@bnorm _ _ B a))
                    (bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)).
          apply Qle_refl.
      + (* case K < m': tail(0,m') = tail(0,K) + tail(K,m'), geom2 at K *)
        apply Qplus_le_compat; [apply Qle_refl | ].
        rewrite (qeqT_imp_qeq _ _
                   (bxcd_qtail_add (@bnorm _ _ B a) 0%nat K m'
                      ltac:(apply NatLe_lift; lia)
                      ltac:(apply NatLe_lift; exact (Nat.lt_le_incl K m' HmK)))).
        apply Qplus_le_compat; [apply Qle_refl
                               | exact (QleT'_to_Qle _ _
                                          (exp_tail_abs_geom2 (@bnorm _ _ B a) K m'
                                             Hc0 Harch (Nat.lt_le_incl K m' HmK)))]. }
  assert (HE0 : Qle 0 (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                       + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q).
  { apply (@Qplus_le_compat 0%Q (exp_tail_abs 0%nat K (@bnorm _ _ B a))
              0%Q (bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)).
    ++ apply QleT'_to_Qle. apply bxcd_qtail_ge0. exact Hc0.
    ++ exact (QleT'_to_Qle _ _
               (q_pow_fact2_nonneg (@bnorm _ _ B a) K Hc0)). }
  assert (HEpos : Qle 0 (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                              + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q).
  { apply (Qle_trans _ 1%Q).
    - exact (Qlt_le_weak 0%Q 1%Q H01).
    - exact (Qle_plus_nonneg_r 1%Q (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                     + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q HE0). }
  assert (HEposT : QleT' 0 (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                              + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q)
    by (apply Qle_to_QleT'; exact HEpos).
  assert (Heq : ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                        + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                 + (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                         + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)))%Q
              == ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                        + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                  * (1 + 1))%Q) by ring.
  assert (HED : Qlt ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                            + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                     + (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                             + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)))
                    (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                            + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                      * (1 + 1))%Q + 1)).
  { rewrite Heq.
    pose proof (proj2 (Qplus_lt_r 0%Q 1%Q
                  ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                          + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                   * (1 + 1))%Q) H01) as Hlt1.
    rewrite (Qplus_0_r ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                              + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                        * (1 + 1))%Q) in Hlt1.
    exact Hlt1. }
  assert (HD : Qlt 0 (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                               + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                        * (1 + 1))%Q + 1)).
  { apply (Qlt_le_trans _
             (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                    + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))).
    - exact (Qlt_le_trans 0%Q 1%Q
               (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                      + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)) H01
               (Qle_plus_nonneg_r 1%Q (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                    + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)%Q HE0)).
    - rewrite <- Heq.
      apply (Qle_trans _
               ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                      + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                + (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                        + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)))%Q).
      + apply Qle_plus_nonneg_r. exact HEpos.
      + apply Qle_plus_nonneg_r. exact (Qlt_le_weak 0%Q 1%Q H01). }
  assert (Heps : QltT 0 (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                 + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                          * (1 + 1))%Q + 1))).
  { apply ncv_qmult_lt0.
    - exact (QltT_to_Qlt _ _ Hq).
    - apply Qinv_lt_0_compat. exact HD. }
  destruct (arch_decay (bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)
              (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                               + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                        * (1 + 1))%Q + 1))
              (q_pow_fact2_nonneg (@bnorm _ _ B a) K Hc0)
              Heps
   ) as [t Hdec].
  exists (2 * (K + Datatypes.S t))%nat.
  intros n HN. apply NatLe_drop in HN.
  pose proof (Nat.div2_odd n) as Hodd.
  assert (HkM : (K + Datatypes.S t <= Nat.div2 n)%nat).
  { destruct (Nat.odd n); cbn [Nat.b2n] in Hodd; lia. }
  assert (Hk2 : (2 * K <= n)%nat) by lia.
  assert (Hlt : Qlt (exp_tail_abs (Nat.div2 n) n (@bnorm _ _ B a))
                    (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                   + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                            * (1 + 1))%Q + 1))).
  { apply (Qle_lt_trans _
             ((q_pow (@bnorm _ _ B a) (Nat.div2 n) / q_fact (Nat.div2 n))
              * (1 + 1))%Q).
    - exact (QleT'_to_Qle _ _
               (exp_tail_abs_geom2 (@bnorm _ _ B a) (Nat.div2 n) n Hc0
                 (fun u Hu => Harch u
                    (NatLe_lift _ _ (Nat.le_trans K (Nat.div2 n) u
                       (Nat.le_trans K (K + Datatypes.S t) (Nat.div2 n)
                          (Nat.le_add_r K (Datatypes.S t)) HkM)
                       (NatLe_drop _ _ Hu))))
                 ltac:(pose proof (Nat.div2_odd n) as Hd;
                       destruct (Nat.odd n); cbn [Nat.b2n] in Hd; lia))).
    - exact (QltT_to_Qlt _ _
               (exp_tail_arch (@bnorm _ _ B a) K t (Nat.div2 n)
                  (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                   + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                            * (1 + 1))%Q + 1))
                  Hc0 Harch Heps Hdec HkM)). }
  pose proof (bxcd_Q2_bound_M (@bnorm _ _ B a) K n
                (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                      + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q
                Hc0 Harch HEposT HE2 HE (NatLe_lift _ _ Hk2)) as HQ2.
  pose proof (bxcd_prod_split _ _ B a n) as Hsplit.
  pose proof (bxcd_prod_close _ _ B a n (bxcd_U _ _ B a n) Hsplit) as Hclose.
  eapply (QeqT_Qlt_bool_cong _ _ _ (qeqT_sym_hw _ _ Hclose)).
  apply Qlt_to_QltT.
  apply (Qle_lt_trans _
           (ncv_qsum (fun j : nat =>
               ncv_qsum (fun i : nat =>
                  if Nat.ltb (Nat.sub n j) i
                  then (bxcd_A (@bnorm _ _ B a) j * bxcd_A (@bnorm _ _ B a) i)%Q
                  else 0%Q) (Datatypes.S n)) (Datatypes.S n)) q).
  - exact (QleT'_to_Qle _ _ (bxcd_U_norm_le _ _ B a (@bnorm _ _ B a) n id_refl)).
  - assert (Htl : Qle (exp_tail_abs (Nat.div2 n) n (@bnorm _ _ B a))
                      (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                       + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                                * (1 + 1))%Q + 1)))
      by (apply Qlt_le_weak; exact Hlt).
    assert (HtlT : QleT' (exp_tail_abs (Nat.div2 n) n (@bnorm _ _ B a))
                         (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                         + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                                  * (1 + 1))%Q + 1)))
      by (apply Qle_to_QleT'; exact Htl).
    eapply Qle_lt_trans.
    + apply QleT'_to_Qle. exact HQ2.
    + eapply Qle_lt_trans.
      * apply Qplus_le_compat.
        -- exact (QleT'_to_Qle _ _
                    (bxcd_Qmult_le_compat_l
                       (exp_tail_abs (Nat.div2 n) n (@bnorm _ _ B a))
                       (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                        + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                                * (1 + 1))%Q + 1))
                       (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                             + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q
                       HEposT HtlT)).
        -- exact (QleT'_to_Qle _ _
                    (bxcd_Qmult_le_compat_l
                       (exp_tail_abs (Nat.div2 n) n (@bnorm _ _ B a))
                       (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                        + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                                * (1 + 1))%Q + 1))
                       (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                             + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q
                       HEposT HtlT)).
      * assert (Hgen : forall u1 v1 : Q,
                     (u1 * v1 + u1 * v1)%Q == ((u1 + u1) * v1)%Q)
            by (intros u1 v1; ring).
        rewrite (Hgen (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))%Q
                      (q * / (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                       + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                                * (1 + 1))%Q + 1))).
        exact (QltT_to_Qlt _ _
                 (bxcd_q_div_lt
                    ((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                           + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                     + (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                             + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q)))
                    (((1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                            + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                      * (1 + 1))%Q + 1) q
                    Hq
                    (Qle_to_QleT' _ _
                       (Qplus_le_compat
                          0%Q (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                    + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                          0%Q (1 + (exp_tail_abs 0%nat K (@bnorm _ _ B a)
                                    + bxcd_A (@bnorm _ _ B a) K * (1 + 1)%Q))
                          HEpos HEpos))
                    (Qlt_to_QltT _ _ HED)
                    (Qlt_to_QltT _ _ HD))).
Qed.

(* ToyR audit trace: assumption-face print of one inventory item;
   expected reading: fully closed. *)
Print Assumptions bxcd_bsum_snoc.
