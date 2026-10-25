(* ConstructiveWorld-Set — exponential series in a Banach algebra. *)

(** * UpReqBanachExp: the exponential series over a Banach algebra.

    Mission.  The Banach-algebra interface [BanachAlg] (carrier [BA],
 carrier equality [bae], addition, noncommutative multiplication,
 additive inverses, scalar embedding [bcoef], norm [bnorm], and the
 completeness field [bcauchy_complete]); partial sums of the
 exponential series [exp_series_partial] with tail bounds
 [esp_diff_le_tail]; the Cauchy property of the partial-sum sequence
 [exp_series_cauchy]; the coefficient identity [bnorm_coef_qeq].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs],
 [Arith.Arith], [Lia].  Requires [S01_BaseRing],
 [S02_CauchyComplete], [S03_QExp] of this development.

    References.  This development, UpReqBanachExp.v, the baseline
 module in ConstructiveWorld-Main whose statement names are carried
 over here verbatim.  Unlike the baseline, the interface takes the
 carrier and its equality as explicit parameters of [BanachAlg]: a
 record field of sort [Set] has no computational content after
 extraction, while parameters do.

    Constructivity.  All named statements and fields are carried by
 [Set] (decidable Q-carriers [QltT]/[QleT']/[QeqT], [Id], [NatLe],
 [sigT]); statements extract with [Obj.magic] = 0 and no
 [type _ = __] erasure; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachExp.v]
 compiles cleanly (exit 0); artifact magic [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ==================== Section 1. The Banach algebra interface ==================== *)
(*  First-use names in this development: bpow, bnorm, bae, bcoef,                    *)
(*  bcauchy, blim.                                                                   *)

Class BanachAlg (BA : Set) (bae : BA -> BA -> Set) := {
  bae_refl   : forall a : BA, bae a a;
  bae_sym    : forall a b : BA, bae a b -> bae b a;
  bae_trans  : forall a b c : BA, bae a b -> bae b c -> bae a c;

  bzero : BA;                              (* additive zero *)
  bone : BA;                               (* multiplicative unit *)
  bplus : BA -> BA -> BA;                  (* addition *)
  bmult : BA -> BA -> BA;                  (* multiplication (noncommutative) *)
  bopp : BA -> BA;                         (* additive inverse *)

  bcoef : Q -> BA;                         (* scalar embedding of the coefficients 1/k! *)
  bnorm : BA -> Q;                         (* Q-valued norm *)

  (* ---- Additive group laws (over the carrier equality bae) ---- *)
  bplus_assoc : forall a b c : BA,
    bae (bplus a (bplus b c)) (bplus (bplus a b) c);
  bplus_comm  : forall a b : BA, bae (bplus a b) (bplus b a);
  bplus_zero  : forall a : BA, bae (bplus a bzero) a;
  bplus_opp   : forall a : BA, bae (bplus a (bopp a)) bzero;

  (* ---- Multiplicative monoid and both distributivities ---- *)
  bmult_assoc : forall a b c : BA,
    bae (bmult a (bmult b c)) (bmult (bmult a b) c);
  bmult_one_l : forall a : BA, bae (bmult bone a) a;
  bmult_one_r : forall a : BA, bae (bmult a bone) a;
  bdistrib_l  : forall a b c : BA,
    bae (bmult a (bplus b c)) (bplus (bmult a b) (bmult a c));
  bdistrib_r  : forall a b c : BA,
    bae (bmult (bplus a b) c) (bplus (bmult a c) (bmult b c));
  bmult_zero  : forall a : BA, bae (bmult a bzero) bzero;

  (* ---- Congruence of the operations for the carrier equality ---- *)
  bplus_wd : forall a b c d : BA,
    bae a c -> bae b d -> bae (bplus a b) (bplus c d);
  bmult_wd : forall a b c d : BA,
    bae a c -> bae b d -> bae (bmult a b) (bmult c d);
  bopp_wd  : forall a b : BA, bae a b -> bae (bopp a) (bopp b);
  bnorm_wd : forall a b : BA, bae a b -> QeqT (bnorm a) (bnorm b);

  (* ---- Scalar embedding laws ---- *)
  bcoef_zero : bae (bcoef 0%Q) bzero;
  bcoef_one  : bae (bcoef 1%Q) bone;
  bcoef_mult : forall q r : Q, bae (bcoef (q * r)%Q) (bmult (bcoef q) (bcoef r));
  bcoef_comm : forall (q : Q) (a : BA), bae (bmult a (bcoef q)) (bmult (bcoef q) a);

  bcoef_plus : forall q r : Q, bae (bplus (bcoef q) (bcoef r)) (bcoef (q + r)%Q);
  bcoef_wd   : forall q r : Q, QeqT q r -> bae (bcoef q) (bcoef r);

  (* ---- Norm laws (QleT' comparison face) ---- *)
  bnorm_zero : Id (bnorm bzero) 0%Q;
  bnorm_one  : Id (bnorm bone) 1%Q;
  bnorm_opp  : forall a : BA, Id (bnorm (bopp a)) (bnorm a);
  bnorm_pos  : forall a : BA, QleT' 0 (bnorm a);
  bnorm_plus : forall a b : BA,
    QleT' (bnorm (bplus a b)) (bnorm a + bnorm b)%Q;             (* subadditivity *)
  bnorm_mult : forall a b : BA,
    QleT' (bnorm (bmult a b)) (bnorm a * bnorm b)%Q;             (* submultiplicativity *)
  bnorm_coef : forall q : Q, QeqT (bnorm (bcoef q)) (Qabs q);

  (* ---- Completeness (explicit Cauchy/limit interface, S02 cauchy inlined) ---- *)
  bcauchy_complete :
    forall (u : nat -> BA),
      (forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall m n : nat,
          NatLe N m -> NatLe N n ->
          QltT (bnorm (bplus (u m) (bopp (u n)))) eps)) ->
      sigT (fun l : BA => forall eps : Q, QltT 0 eps ->
        sigT (fun N : nat => forall n : nat,
          NatLe N n -> QltT (bnorm (bplus (u n) (bopp l))) eps));
}.

(* The three congruence lemmas below transport [QltT]/[QleT'] conclusions *)
(* across [QeqT]-related bounds, so that norm identities can be used to   *)
(* rewrite comparison goals.                                              *)

Lemma qeqT_sym_hw : forall x y : Q, QeqT x y -> QeqT y x.
Proof. intros x y H. apply qeq_imp_qeqT. apply Qeq_sym. apply qeqT_imp_qeq. exact H. Qed.

Lemma QeqT_Qlt_bool_cong : forall x y k : Q, QeqT x y -> QltT x k -> QltT y k.
Proof.
  intros x y k Hxy Hx.
  apply Qlt_to_QltT.
  apply (Qle_lt_trans y x k).
  - apply QleT'_to_Qle. apply qeq_le. apply qeqT_sym_hw. exact Hxy.
  - apply QltT_to_Qlt. exact Hx.
Qed.

Lemma QeqT_Qle_bool_cong : forall x y k : Q, QeqT x y -> QleT' x k -> QleT' y k.
Proof.
  intros x y k Hxy Hx.
  apply Qle_to_QleT'.
  apply (Qle_trans y x k).
  - apply QleT'_to_Qle. apply qeq_le. apply qeqT_sym_hw. exact Hxy.
  - apply QleT'_to_Qle. exact Hx.
Qed.

Lemma QeqT_Qle_bool_cong_r : forall x y k : Q, QeqT x y -> QleT' k x -> QleT' k y.
Proof.
  intros x y k Hxy Hx.
  apply Qle_to_QleT'.
  apply (Qle_trans k x y).
  - apply QleT'_to_Qle. exact Hx.
  - apply QleT'_to_Qle. apply qeq_le. exact Hxy.
Qed.

(* The norm respects the carrier equality, in QeqT face. *)
Lemma bnorm_wd_qeq : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b : BA), bae a b -> QeqT (@bnorm BA bae B a) (@bnorm BA bae B b).
Proof. intros BA bae B a b H. apply (@bnorm_wd BA bae B a b H). Qed.

(* The norm of an embedded scalar is the rational absolute value. *)
Lemma bnorm_coef_qeq : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (q : Q), QeqT (@bnorm BA bae B (@bcoef BA bae B q)) (Qabs q).
Proof. intros BA bae B q. apply (@bnorm_coef BA bae B q). Qed.

(* Cauchy and limit predicates in named form (isomorphic to the body of   *)
(* the completeness field).                                               *)
Definition bcauchy (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
           (u : nat -> BA) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (@bnorm BA bae B (@bplus BA bae B (u m) (@bopp BA bae B (u n)))) eps).

Definition blim (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
           (u : nat -> BA) (l : BA) : Set :=
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall n : nat,
      NatLe N n -> QltT (@bnorm BA bae B (@bplus BA bae B (u n) (@bopp BA bae B l))) eps).

(* The completeness field, repackaged in the named Cauchy/limit form. *)
Lemma bcauchy_complete_sig : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (u : nat -> BA), bcauchy BA bae B u -> sigT (fun l : BA => blim BA bae B u l).
Proof.
  intros BA bae B u Hu. exact (@bcauchy_complete BA bae B u Hu).
Qed.

(* ==================== Section 2. Additive group engine ==================== *)

Lemma bplus_wd_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b c : BA), bae a b -> bae (@bplus BA bae B a c) (@bplus BA bae B b c).
Proof.
  intros BA bae B a b c H. exact (@bplus_wd BA bae B a c b c H (@bae_refl BA bae B c)).
Qed.

Lemma bplus_wd_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b c : BA), bae a b -> bae (@bplus BA bae B c a) (@bplus BA bae B c b).
Proof.
  intros BA bae B a b c H. exact (@bplus_wd BA bae B c a c b (@bae_refl BA bae B c) H).
Qed.

Lemma bplus_zero_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA), bae (@bplus BA bae B (@bzero BA bae B) a) a.
Proof.
  intros BA bae B a.
  exact (@bae_trans BA bae B _ _ _
           (@bplus_comm BA bae B (@bzero BA bae B) a) (@bplus_zero BA bae B a)).
Qed.

Lemma bopp_unique : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (z w : BA), bae (@bplus BA bae B z w) (@bzero BA bae B) -> bae z (@bopp BA bae B w).
Proof.
  intros BA bae B z w H.
  (* z = z+0 = z+(w+(-w)) = (z+w)+(-w) = 0+(-w) = (-w)+0 = -w *)
  eapply (@bae_trans BA bae B).
  { exact (@bae_sym BA bae B _ _ (@bplus_zero BA bae B z)). }
  eapply (@bae_trans BA bae B).
  { exact (@bplus_wd_r BA bae B (@bzero BA bae B) (@bplus BA bae B w (@bopp BA bae B w)) z
             (@bae_sym BA bae B _ _ (@bplus_opp BA bae B w))). }
  eapply (@bae_trans BA bae B).
  { exact (@bplus_assoc BA bae B z w (@bopp BA bae B w)). }
  eapply (@bae_trans BA bae B).
  { exact (@bplus_wd_l BA bae B (@bplus BA bae B z w) (@bzero BA bae B) (@bopp BA bae B w) H). }
  eapply (@bae_trans BA bae B).
  { exact (@bplus_comm BA bae B (@bzero BA bae B) (@bopp BA bae B w)). }
  exact (@bplus_zero BA bae B (@bopp BA bae B w)).
Qed.

Lemma bplus_middle_swap : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b c : BA), bae (@bplus BA bae B (@bplus BA bae B a b) c)
                    (@bplus BA bae B (@bplus BA bae B a c) b).
Proof.
  intros BA bae B a b c.
  (* (a+b)+c = a+(b+c) = a+(c+b) = (a+c)+b *)
  eapply (@bae_trans BA bae B).
  { exact (@bae_sym BA bae B _ _ (@bplus_assoc BA bae B a b c)). }
  eapply (@bae_trans BA bae B).
  { exact (@bplus_wd_r BA bae B (@bplus BA bae B b c) (@bplus BA bae B c b) a (@bplus_comm BA bae B b c)). }
  exact (@bplus_assoc BA bae B a c b).
Qed.

(* Moving an additively inverted summand to the outside:                  *)
(* (-a)+b = -(a+(-b)).                                                    *)
Lemma bplus_opp_swap : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a b : BA), bae (@bplus BA bae B (@bopp BA bae B a) b)
                  (@bopp BA bae B (@bplus BA bae B a (@bopp BA bae B b))).
Proof.
  intros BA bae B a b.
  apply (@bopp_unique BA bae B (@bplus BA bae B (@bopp BA bae B a) b)
                      (@bplus BA bae B a (@bopp BA bae B b))).
  (* (-a+b)+(a+(-b)) = 0, by six reassociations *)
  eapply (@bae_trans BA bae B).
  { (* = (-a) + (b + (a+(-b))) *)
    exact (@bae_sym BA bae B _ _
             (@bplus_assoc BA bae B (@bopp BA bae B a) b (@bplus BA bae B a (@bopp BA bae B b)))). }
  eapply (@bae_trans BA bae B).
  { (* = (-a) + ((b+a) + (-b)) *)
    exact (@bplus_wd_r BA bae B (@bplus BA bae B b (@bplus BA bae B a (@bopp BA bae B b)))
                         (@bplus BA bae B (@bplus BA bae B b a) (@bopp BA bae B b))
                         (@bopp BA bae B a) (@bplus_assoc BA bae B b a (@bopp BA bae B b))). }
  eapply (@bae_trans BA bae B).
  { (* = (-a) + ((a+b) + (-b)) *)
    exact (@bplus_wd_r BA bae B (@bplus BA bae B (@bplus BA bae B b a) (@bopp BA bae B b))
                         (@bplus BA bae B (@bplus BA bae B a b) (@bopp BA bae B b))
                         (@bopp BA bae B a)
                         (@bplus_wd_l BA bae B (@bplus BA bae B b a) (@bplus BA bae B a b)
                                        (@bopp BA bae B b) (@bplus_comm BA bae B b a))). }
  eapply (@bae_trans BA bae B).
  { (* = ((-a) + (a+b)) + (-b) *)
    exact (@bplus_assoc BA bae B (@bopp BA bae B a) (@bplus BA bae B a b) (@bopp BA bae B b)). }
  eapply (@bae_trans BA bae B).
  { (* = (((-a)+a)+b) + (-b) *)
    exact (@bplus_wd_l BA bae B (@bplus BA bae B (@bopp BA bae B a) (@bplus BA bae B a b))
                         (@bplus BA bae B (@bplus BA bae B (@bopp BA bae B a) a) b)
                         (@bopp BA bae B b) (@bplus_assoc BA bae B (@bopp BA bae B a) a b)). }
  (* = (0+b)+(-b) = b+(-b) = 0 *)
  exact (@bae_trans BA bae B _ _ _
           (@bplus_wd_l BA bae B (@bplus BA bae B (@bplus BA bae B (@bopp BA bae B a) a) b)
                          (@bplus BA bae B (@bzero BA bae B) b)
                          (@bopp BA bae B b)
                          (@bplus_wd_l BA bae B (@bplus BA bae B (@bopp BA bae B a) a)
                                         (@bzero BA bae B) b
                                         (@bae_trans BA bae B _ _ _
                                            (@bplus_comm BA bae B (@bopp BA bae B a) a)
                                            (@bplus_opp BA bae B a))))
           (@bae_trans BA bae B _ _ _
              (@bplus_wd_l BA bae B (@bplus BA bae B (@bzero BA bae B) b) b (@bopp BA bae B b)
                             (bplus_zero_l BA bae B b))
              (@bplus_opp BA bae B b))).
Qed.

(* ==================== Section 3. Partial sums, tail bounds, Cauchy property ==================== *)
(*  Q-level engine reused from S03: q_pow, q_fact, exp_tail_abs,          *)
(*  q_arch_geom, arch_decay, exp_tail_arch, exp_tail_abs_geom2,           *)
(*  exp_tail_abs_le_m, q_fact_pos.                                        *)

Fixpoint bpow (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (n : nat) : BA :=
  match n with
  | 0%nat => @bone BA bae B
  | Datatypes.S m => @bmult BA bae B (bpow BA bae B a m) a
  end.

Fixpoint exp_series_partial (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
           (a : BA) (n : nat) : BA :=
  match n with
  | 0%nat => @bone BA bae B
  | Datatypes.S m =>
      @bplus BA bae B (exp_series_partial BA bae B a m)
        (@bmult BA bae B (bpow BA bae B a (Datatypes.S m))
                  (@bcoef BA bae B (/ q_fact (Datatypes.S m))))
  end.

(* Norm of a power: the norm is submultiplicative, so n-fold products    *)
(* satisfy a norm bound by induction on k. *)
Lemma bnorm_bpow : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA) (k : nat), QleT' (@bnorm BA bae B (bpow BA bae B a k)) (q_pow (@bnorm BA bae B a) k).
Proof.
  intros BA bae B a k. induction k as [| m IH].
  - change (bpow BA bae B a 0%nat) with (@bone BA bae B).
    rewrite (@bnorm_one BA bae B). apply qleT'_refl.
  - change (bpow BA bae B a (Datatypes.S m)) with (@bmult BA bae B (bpow BA bae B a m) a).
    change (q_pow (@bnorm BA bae B a) (Datatypes.S m))
      with ((@bnorm BA bae B a) * q_pow (@bnorm BA bae B a) m)%Q.
    eapply qleT'_trans.
    + exact (@bnorm_mult BA bae B (bpow BA bae B a m) a).
    + apply Qle_to_QleT'.
      apply (Qle_trans _ ((q_pow (@bnorm BA bae B a) m) * (@bnorm BA bae B a))%Q).
      * apply (Qmult_le_compat_r (@bnorm BA bae B (bpow BA bae B a m))
                                 (q_pow (@bnorm BA bae B a) m) (@bnorm BA bae B a)).
        -- apply QleT'_to_Qle. exact IH.
        -- apply QleT'_to_Qle. apply (@bnorm_pos BA bae B a).
      * apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. ring.
Qed.

(* Norm of a series term: the k-th summand is bounded by the Q-level     *)
(* term of the scalar tail series. *)
Lemma bnorm_esp_term : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA) (k : nat),
  QleT' (@bnorm BA bae B (@bmult BA bae B (bpow BA bae B a (Datatypes.S k))
                            (@bcoef BA bae B (/ q_fact (Datatypes.S k)))))
        (q_pow (@bnorm BA bae B a) (Datatypes.S k) / q_fact (Datatypes.S k)).
Proof.
  intros BA bae B a k.
  apply (qleT'_trans _ _ _
    (@bnorm_mult BA bae B (bpow BA bae B a (Datatypes.S k))
                   (@bcoef BA bae B (/ q_fact (Datatypes.S k))))).
  apply Qle_to_QleT'.
  apply (Qle_trans _
    ((q_pow (@bnorm BA bae B a) (Datatypes.S k))
       * (@bnorm BA bae B (@bcoef BA bae B (/ q_fact (Datatypes.S k)))))%Q).
  - apply (Qmult_le_compat_r (@bnorm BA bae B (bpow BA bae B a (Datatypes.S k)))
                             (q_pow (@bnorm BA bae B a) (Datatypes.S k))
                             (@bnorm BA bae B (@bcoef BA bae B (/ q_fact (Datatypes.S k))))).
    + apply QleT'_to_Qle. apply (bnorm_bpow BA bae B a (Datatypes.S k)).
    + apply QleT'_to_Qle. apply (@bnorm_pos BA bae B (@bcoef BA bae B (/ q_fact (Datatypes.S k)))).
  - apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT.
    assert (Hbq : @bnorm BA bae B (bcoef (/ q_fact (Datatypes.S k))) == Qabs (/ q_fact (Datatypes.S k)))
      by (apply qeqT_imp_qeq; apply bnorm_coef_qeq).
    rewrite Hbq.
    assert (Hq : 0 <= / q_fact (Datatypes.S k))
      by (apply Qlt_le_weak; apply Qinv_lt_0_compat; apply QltT_to_Qlt; apply q_fact_pos).
    rewrite (Qabs_pos (/ q_fact (Datatypes.S k)) Hq).
    reflexivity.
Qed.

(* Main tail bound: m <= n implies the norm of the difference of the     *)
(* partial sums is bounded by the scalar tail sum over k = m+1..n. *)
Lemma esp_diff_le_tail : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA) (m n : nat), (m <= n)%nat ->
  QleT' (@bnorm BA bae B (@bplus BA bae B (exp_series_partial BA bae B a n)
                            (@bopp BA bae B (exp_series_partial BA bae B a m))))
        (exp_tail_abs m n (@bnorm BA bae B a)).
Proof.
  intros BA bae B a m n Hm. revert m Hm.
  induction n as [| n' IH]; intros m Hm.
  - (* n = 0 forces m = 0, and the difference is zero *)
    assert (Hm0 : m = 0%nat) by lia. subst m.
    pose proof (@bnorm_wd BA bae B _ _ (@bplus_opp BA bae B (exp_series_partial BA bae B a 0))) as Hwd0.
    eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ Hwd0)).
    apply Qle_to_QleT'.
    rewrite (@bnorm_zero BA bae B).
    apply Qle_refl.
  - destruct (Nat.eq_dec m (Datatypes.S n')) as [Heq | Hne].
    + (* m = S n': the difference is zero and the tail sum equals zero *)
      subst m.
      pose proof (@bnorm_wd BA bae B _ _
        (@bplus_opp BA bae B (exp_series_partial BA bae B a (Datatypes.S n')))) as HwdS.
      eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ HwdS)).
      apply Qle_to_QleT'.
      rewrite (@bnorm_zero BA bae B).
      rewrite (qeqT_imp_qeq _ _
                 (exp_tail_abs_le_m (Datatypes.S n') (Datatypes.S n')
                    (@bnorm BA bae B a) (Nat.le_refl _))).
      apply Qle_refl.
    + (* m <= n': peel off the last term, swap the middle summands, and  *)
      (* apply the triangle inequality term by term *)
      assert (Hmn' : (m <= n')%nat) by lia.
      assert (Hleb : Nat.leb m n' = true) by (apply Nat.leb_le; exact Hmn').
      change (exp_series_partial BA bae B a (Datatypes.S n'))
        with (@bplus BA bae B (exp_series_partial BA bae B a n')
                (@bmult BA bae B (bpow BA bae B a (Datatypes.S n'))
                          (@bcoef BA bae B (/ q_fact (Datatypes.S n'))))).
      pose proof (@bnorm_wd BA bae B _ _
        (bplus_middle_swap BA bae B (exp_series_partial BA bae B a n')
            (@bmult BA bae B (bpow BA bae B a (Datatypes.S n'))
                      (@bcoef BA bae B (/ q_fact (Datatypes.S n'))))
            (@bopp BA bae B (exp_series_partial BA bae B a m)))) as HwdM.
      eapply (QeqT_Qle_bool_cong _ _ _ (qeqT_sym_hw _ _ HwdM)).
      eapply qleT'_trans.
      * (* triangle: the sum of the two norms bounds the norm of the sum *)
        exact (@bnorm_plus BA bae B
                 (@bplus BA bae B (exp_series_partial BA bae B a n')
                          (@bopp BA bae B (exp_series_partial BA bae B a m)))
                 (@bmult BA bae B (bpow BA bae B a (Datatypes.S n'))
                            (@bcoef BA bae B (/ q_fact (Datatypes.S n'))))).
      * (* the two bounds add, and the right side matches the tail sum    *)
        (* definitionally once the leb test resolves to true *)
        change (exp_tail_abs m (Datatypes.S n') (@bnorm BA bae B a))
          with ((exp_tail_abs m n' (@bnorm BA bae B a))
                + (if Nat.leb m n'
                   then q_pow (@bnorm BA bae B a) (Datatypes.S n') / q_fact (Datatypes.S n')
                   else 0)%Q).
        rewrite Hleb.
        apply (qleT'_plus_compat _ _ _ _).
        -- exact (IH m Hmn').
        -- exact (bnorm_esp_term BA bae B a n').
Qed.

(* Main statement: the partial sums of the exponential series form a     *)
(* Cauchy sequence in the Banach algebra. *)
Lemma exp_series_cauchy : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae)
  (a : BA), bcauchy BA bae B (fun n => exp_series_partial BA bae B a n).
Proof.
  intros BA bae B a eps Heps.
  assert (Hr : Qle 0 (@bnorm BA bae B a)) by (apply QleT'_to_Qle; apply (@bnorm_pos BA bae B a)).
  destruct (q_arch_geom (@bnorm BA bae B a)) as [N0 HN0].
  assert (Harch : forall u : nat, (N0 <= u)%nat ->
            Qle (Qmult (1 + 1)%Q (@bnorm BA bae B a)) (Z.of_nat (u + 1) # 1)).
  { intros u Hu. apply QleT'_to_Qle. apply (HN0 u). apply NatLe_lift. exact Hu. }
  assert (HC : Qle 0 ((q_pow (@bnorm BA bae B a) N0 / q_fact N0) * (1 + 1)%Q))
    by (apply QleT'_to_Qle; apply q_pow_fact2_nonneg; apply (@bnorm_pos BA bae B a)).
  destruct (arch_decay ((q_pow (@bnorm BA bae B a) N0 / q_fact N0) * (1 + 1)%Q) eps
             (Qle_to_QleT' _ _ HC) Heps) as [t Hdec].
  exists (N0 + Datatypes.S t)%nat.
  intros m n Hm Hn.
  apply NatLe_drop in Hm. apply NatLe_drop in Hn.
  assert (HNm : (N0 <= m)%nat) by lia.
  assert (HNn : (N0 <= n)%nat) by lia.
  destruct (Nat.leb m n) eqn:Emn.
  - (* m <= n: symmetrize the difference, then bound the scalar tail *)
    apply Nat.leb_le in Emn.
    pose proof (@bnorm_wd BA bae B _ _
      (@bplus_comm BA bae B (exp_series_partial BA bae B a m)
                    (@bopp BA bae B (exp_series_partial BA bae B a n)))) as HwdC1.
    eapply (QeqT_Qlt_bool_cong _ _ eps (qeqT_sym_hw _ _ HwdC1)).
    pose proof (@bnorm_wd BA bae B _ _
      (bplus_opp_swap BA bae B (exp_series_partial BA bae B a n)
                       (exp_series_partial BA bae B a m))) as HwdC2.
    eapply (QeqT_Qlt_bool_cong _ _ eps (qeqT_sym_hw _ _ HwdC2)).
    rewrite (@bnorm_opp BA bae B (@bplus BA bae B (exp_series_partial BA bae B a n)
                                    (@bopp BA bae B (exp_series_partial BA bae B a m)))).
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow (@bnorm BA bae B a) m / q_fact m) * (1 + 1)%Q) eps).
    + apply QleT'_to_Qle.
      apply (qleT'_trans _ _ _
        (esp_diff_le_tail BA bae B a m n Emn)
        (exp_tail_abs_geom2 (@bnorm BA bae B a) m n
           (Qle_to_QleT' _ _ Hr)
           (fun t Ht => Qle_to_QleT' _ _
              (Harch t (Nat.le_trans N0 m t HNm (NatLe_drop _ _ Ht))))
           Emn)).
    + apply QltT_to_Qlt.
      apply (exp_tail_arch (@bnorm BA bae B a) N0 t m eps
               (Qle_to_QleT' _ _ Hr)
               (fun u Hu => Qle_to_QleT' _ _ (Harch u (NatLe_drop _ _ Hu)))
               Heps Hdec).
      lia.
  - (* n < m: run the same bound with n as the smaller index *)
    apply Nat.leb_gt in Emn.
    assert (Hnm : (n <= m)%nat) by lia.
    apply Qlt_to_QltT.
    apply (Qle_lt_trans _ ((q_pow (@bnorm BA bae B a) n / q_fact n) * (1 + 1)%Q) eps).
    + apply QleT'_to_Qle.
      apply (qleT'_trans _ _ _
        (esp_diff_le_tail BA bae B a n m Hnm)
        (exp_tail_abs_geom2 (@bnorm BA bae B a) n m
           (Qle_to_QleT' _ _ Hr)
           (fun t Ht => Qle_to_QleT' _ _
              (Harch t (Nat.le_trans N0 n t HNn (NatLe_drop _ _ Ht))))
           Hnm)).
    + apply QltT_to_Qlt.
      apply (exp_tail_arch (@bnorm BA bae B a) N0 t n eps
               (Qle_to_QleT' _ _ Hr)
               (fun u Hu => Qle_to_QleT' _ _ (Harch u (NatLe_drop _ _ Hu)))
               Heps Hdec).
      lia.
Qed.

(* Future work.  Two classical companions of the exponential are not     *)
(* included here.  (1) The addition law e^(a+b) = e^a * e^b and the      *)
(* identity (e^a)^(-1) = e^(-a) require, beyond the tail bounds above    *)
(* and the limit extracted via [bcauchy_complete_sig], the binomial      *)
(* identity for (a+b)^n when the products commute (a*b = b*a),           *)
(* together with continuity of multiplication for limits.  (2) The       *)
(* positivity/order structure of C*-algebras (constructive spectral      *)
(* theory) is an open problem and is not attempted.                      *)
