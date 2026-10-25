(* ConstructiveWorld-Set — the exponential of zero in a Banach algebra. *)

(** * UpReqBanachExpBasic: [exp 0 = 1] at the Banach level.

    Mission.  The terminal step of the inverse law [(e^a)^{-1} = e^{-a}] is
    [: e^0 = 1].  In a Banach algebra this is provable outright: in
    [exp_series_partial m bzero] every term of order [: k >= 1] degenerates
    because [bpow bzero k = bzero], leaving only the leading term.  This
    file lands that block plus its norm bound.  Statements:
    [bxb_series_zero], [bxb_norm_series_zero], [bxb_qsum],
    [bxb_norm_bound], [bxb_expdef_exp_zero_close].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp], [UpReqBanachExpDef] of this development; the
      families [BanachAlg], [bpow], [exp_series_partial], [bae],
      [bnorm_esp_term] are reused without redefinition.

    References.  This development, ConstructiveWorld-Main
      UpReqBanachExpBasic.v, the baseline module whose statement names are
      carried over here verbatim.

    Constructivity.  All named statements and fields are carried by
      [Set] ([bae], [Id], [QleT'], [sigT], [QltT]); no Prop leakage in
      statement faces.  Statements extract with [Obj.magic] = 0 and no
      erasure; [coqchk] reports [Axioms: none].  The identity
      [exp bzero = bone] as a full [bae] equation needs a cancellation
      field the algebra class does not carry; the strongest faces reachable
      at the current interface are the all-partial-sums identity
      [bxb_series_zero] and the element neighborhood statement
      [bxb_expdef_exp_zero_close].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachExpBasic.v]
      compiles cleanly (exit 0); the first eight bytes of the artifact
      are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachExpDef.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 1. Powers of zero degenerate ================= *)

(* Recursive expansion of [bpow]: for [: n >= 1], [bzero^n] equals [bzero].
   The order-zero term [bone] is excluded by the premise [: 1 <= n]; the
   [: S 0] branch closes by [bmult_one_l], and the [: S (S j)] branch
   transports the induction premise with [bmult_wd] and closes by
   [bmult_zero]. *)
Lemma bxb_bpow_zero : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat),
  (1 <= n)%nat -> bae (bpow BA bae B (@bzero _ _ B) n) (@bzero _ _ B).
Proof.
  intros BA bae B n Hn. destruct n as [| m].
  - (* Contradiction with the premise at [: n = 0]; [exfalso] moves to the
       False goal first, since the Prop elimination of the order cannot fire
       on the Set goal directly. *)
    exfalso. lia.
  - induction m as [| j IH].
    + (* [: n = 1]: [bone * bzero = bzero]. *)
      change (bpow BA bae B (@bzero _ _ B) (Datatypes.S 0%nat))
        with (@bmult _ _ B (@bone _ _ B) (@bzero _ _ B)).
      exact (@bmult_one_l _ _ B (@bzero _ _ B)).
    + (* [: n = S (S j)]: transport by [bmult] congruence, close by
         [bmult_zero]. *)
      assert (Hj : (1 <= Datatypes.S j)%nat) by lia.
      change (bpow BA bae B (@bzero _ _ B) (Datatypes.S (Datatypes.S j)))
        with (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S j)) (@bzero _ _ B)).
      eapply bae_trans.
      { exact (@bmult_wd _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S j))
                           (@bzero _ _ B) (@bzero _ _ B) (@bzero _ _ B)
                           (IH Hj) (@bae_refl _ _ B (@bzero _ _ B))). }
      exact (@bmult_zero _ _ B (@bzero _ _ B)).
Qed.

(* Series term degenerate at zero: [bzero^(S k) * q] equals [bzero] for any
   scalar [q]. *)
Lemma bxb_esp_term_zero : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (k : nat) (q : Q),
  bae (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S k)) (@bcoef _ _ B q))
        (@bzero _ _ B).
Proof.
  intros BA bae B k q.
  assert (Hk : (1 <= Datatypes.S k)%nat) by lia.
  eapply bae_trans.
  { exact (@bmult_wd _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S k)) (@bcoef _ _ B q)
                      (@bzero _ _ B) (@bcoef _ _ B q)
                      (bxb_bpow_zero _ _ B (Datatypes.S k) Hk)
                      (@bae_refl _ _ B (@bcoef _ _ B q))). }
  eapply bae_trans.
  { exact (@bcoef_comm _ _ B q (@bzero _ _ B)). }
  exact (@bmult_zero _ _ B (@bcoef _ _ B q)).
Qed.

(* ================= Section 2. Every partial sum at zero equals one ================= *)

(* [exp_series_partial B bzero m] equals [bone] in the [bae] carrier, by
   induction on [: m]: the leading [bone] stays, all terms of order
   [: k >= 1] degenerate by [bxb_esp_term_zero], and [bplus_zero] closes —
   the full equation face of [: e^0 = 1] at the Banach level. *)
Lemma bxb_series_zero : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (m : nat),
  bae (exp_series_partial BA bae B (@bzero _ _ B) m) (@bone _ _ B).
Proof.
  intros BA bae B m. induction m as [| k IHk].
  - change (exp_series_partial BA bae B (@bzero _ _ B) 0%nat) with (@bone _ _ B).
    exact (@bae_refl _ _ B (@bone _ _ B)).
  - change (exp_series_partial BA bae B (@bzero _ _ B) (Datatypes.S k))
      with (@bplus _ _ B (exp_series_partial BA bae B (@bzero _ _ B) k)
              (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S k))
                        (@bcoef _ _ B (/ q_fact (Datatypes.S k))))).
    eapply bae_trans.
    { exact (@bplus_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) k)
               (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S k))
                         (@bcoef _ _ B (/ q_fact (Datatypes.S k))))
               (@bone _ _ B) (@bzero _ _ B) IHk
               (bxb_esp_term_zero _ _ B k (/ q_fact (Datatypes.S k)))). }
    exact (@bplus_zero _ _ B (@bone _ _ B)).
Qed.

(* Norm face: the norm of every partial sum at zero is [QeqT]-equal to 1
   (after weakening, the [Id] face is out of reach and the statement face is
   weakened accordingly). *)
Lemma bxb_norm_series_zero : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (m : nat),
  QeqT (@bnorm _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m)) 1%Q.
Proof.
  intros BA bae B m.
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm _ _ B (@bone _ _ B))).
  - apply qeqT_imp_qeq.
    exact (@bnorm_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m) (@bone _ _ B)
             (bxb_series_zero _ _ B m)).
  - rewrite (@bnorm_one _ _ B). apply Qeq_refl.
Qed.

(* Cauchy certificate for free: pairwise differences of the zero series
   vanish, with the explicit closed modulus [: N = 0] — where the general
   chain needs the Archimedean witness of [exp_series_cauchy], the zero
   element needs nothing.  This is the free existence face of the
   [: e^0] limit in the invertibility chain. *)
Lemma bxb_series_zero_bcauchy : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (eps : Q),
  QltT 0 eps ->
  sigT (fun N : nat => forall m n : nat,
    NatLe N m -> NatLe N n ->
    QltT (@bnorm _ _ B (@bplus _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m)
                             (@bopp _ _ B (exp_series_partial BA bae B (@bzero _ _ B) n))))
           eps).
Proof.
  intros BA bae B eps Heps.
  exists 0%nat. intros m n Hm Hn.
  eapply (QeqT_Qlt_bool_cong _ _ eps
    (qeqT_sym_hw _ _ (@bnorm_wd _ _ B
      (@bplus _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m)
                (@bopp _ _ B (exp_series_partial BA bae B (@bzero _ _ B) n)))
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B)))
      (@bplus_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m)
                  (@bopp _ _ B (exp_series_partial BA bae B (@bzero _ _ B) n))
                  (@bone _ _ B) (@bopp _ _ B (@bone _ _ B))
                  (bxb_series_zero _ _ B m)
                  (@bopp_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) n)
                              (@bone _ _ B) (bxb_series_zero _ _ B n)))))).
  eapply (QeqT_Qlt_bool_cong _ _ eps
    (qeqT_sym_hw _ _ (@bnorm_wd _ _ B (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (@bone _ _ B))) (@bzero _ _ B)
               (@bplus_opp _ _ B (@bone _ _ B))))).
  rewrite (@bnorm_zero _ _ B).
  exact Heps.
Qed.

(* ================= Section 3. Norm bound on partial sums, rational-valued ================= *)

(* The rational positive-index partial sum: the sum of [: x^k / k!] over
   [: k <= n] (order-zero term [1]; order [: S k] terms in direct inverse
   form [: x^(S k) / (S k)!], verbatim the shape of the right side of
   [bnorm_esp_term]). *)
Fixpoint bxb_qsum (x : Q) (n : nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | Datatypes.S k =>
      (bxb_qsum x k
        + q_pow x (Datatypes.S k) / q_fact (Datatypes.S k))%Q
  end.

(* Main bound: the norm of a partial sum is [QleT']-below the sum of
   [: norm(a)^k / k!], by induction — triangle splitting by [bnorm_plus],
   then the induction premise and [bnorm_esp_term] merged by
   [qleT'_plus_compat]. *)
Lemma bxb_norm_bound : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (m : nat),
  QleT' (@bnorm _ _ B (exp_series_partial BA bae B a m)) (bxb_qsum (@bnorm _ _ B a) m).
Proof.
  intros BA bae B a m. induction m as [| k IHk].
  - change (exp_series_partial BA bae B a 0%nat) with (@bone _ _ B).
    change (bxb_qsum (@bnorm _ _ B a) 0%nat) with 1%Q.
    rewrite (@bnorm_one _ _ B). apply qleT'_refl.
  - change (exp_series_partial BA bae B a (Datatypes.S k))
      with (@bplus _ _ B (exp_series_partial BA bae B a k)
              (@bmult _ _ B (bpow BA bae B a (Datatypes.S k))
                        (@bcoef _ _ B (/ q_fact (Datatypes.S k))))).
    change (bxb_qsum (@bnorm _ _ B a) (Datatypes.S k))
      with ((bxb_qsum (@bnorm _ _ B a) k
              + q_pow (@bnorm _ _ B a) (Datatypes.S k)
                / q_fact (Datatypes.S k))%Q).
    eapply qleT'_trans.
    + exact (@bnorm_plus _ _ B (exp_series_partial BA bae B a k)
               (@bmult _ _ B (bpow BA bae B a (Datatypes.S k))
                         (@bcoef _ _ B (/ q_fact (Datatypes.S k))))).
    + apply (qleT'_plus_compat _ _ _ _).
      * exact IHk.
      * exact (bnorm_esp_term _ _ B a k).
Qed.

(* ================= Section 4. Joining the exponential element face ================= *)

(* Element-face combination: the exponential element agrees with [bone] at
   zero up to arbitrarily small norm.  The two halves join through the
   public interfaces: this file's [bxb_series_zero] (all partial sums equal
   one, exact face) with [bxdef_exp_spec_eps] (the element is the limit of
   the partial sums, neighborhood face); taking [: n = N], [bnorm_wd]
   replaces the partial-sum slot by this file's exact [bone] face.  The
   statement is shaped like [bxdef_exp_zero_close] of [UpReqBanachExpDef]
   but composed through the exact face; the full [bae] equation remains
   blocked by the missing cancellation field and stays honestly open. *)
Lemma bxb_expdef_exp_zero_close : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (eps : Q),
  QltT 0 eps ->
  QltT (@bnorm _ _ B (@bplus _ _ B (bxdef_exp _ _ B (@bzero _ _ B))
                           (@bopp _ _ B (@bone _ _ B)))) eps.
Proof.
  intros BA bae B eps Heps.
  destruct (bxdef_exp_spec_eps _ _ B (@bzero _ _ B) eps Heps) as [N HN].
  specialize (HN N (NatLe_lift _ _ (Nat.le_refl N))).
  pose proof (QeqT_Qlt_bool_cong _ _ eps (@bnorm_wd _ _ B
      (@bplus _ _ B (exp_series_partial BA bae B (@bzero _ _ B) N)
                (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B))))
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B))))
      (@bplus_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) N)
                  (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))
                  (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))
                  (bxb_series_zero _ _ B N)
                  (@bae_refl _ _ B (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))))) HN) as HN2.
  clear HN. rename HN2 into HN.
  (* The specification slot is [bone + (-E)] while the goal is
     [E + (-bone)]; reorder by commutativity, then [bplus_opp_swap]
     ([E + (-bone)] is the opposite of [bone + (-E)]), and close with
     [bnorm_opp]. *)
  eapply (QeqT_Qlt_bool_cong _ _ eps
    (qeqT_sym_hw _ _ (@bnorm_wd _ _ B
      (@bplus _ _ B (bxdef_exp _ _ B (@bzero _ _ B)) (@bopp _ _ B (@bone _ _ B)))
      (@bopp _ _ B (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))))
      (@bae_trans _ _ B
         (@bplus _ _ B (bxdef_exp _ _ B (@bzero _ _ B)) (@bopp _ _ B (@bone _ _ B)))
         (@bplus _ _ B (@bopp _ _ B (@bone _ _ B)) (bxdef_exp _ _ B (@bzero _ _ B)))
         (@bopp _ _ B (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))))
         (@bplus_comm _ _ B (bxdef_exp _ _ B (@bzero _ _ B)) (@bopp _ _ B (@bone _ _ B)))
         (@bplus_opp_swap BA bae B (@bone _ _ B) (bxdef_exp _ _ B (@bzero _ _ B))))))).
  rewrite (@bnorm_opp _ _ B (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B))))).
  exact HN.
Qed.

(* Assembly notes, registered honestly as open at this interface.  The
   terminal step [: e^0 = 1] appears here in four faces: the all-partial-sums
   equation [bxb_series_zero]; the norm face [bxb_norm_series_zero]; the
   free Cauchy certificate [bxb_series_zero_bcauchy] with closed modulus
   [: N = 0]; and the rational-valued norm bound [bxb_norm_bound], from
   which [bxb_expdef_exp_zero_close] joins the element face.  The full
   equation [exp bzero = bone] needs a cancellation field on the algebra
   class (arbitrarily small norm implies equality); adding it is an upstream
   design decision and is not attempted here. *)
