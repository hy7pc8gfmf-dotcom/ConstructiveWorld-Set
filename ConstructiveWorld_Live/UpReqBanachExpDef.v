(* ConstructiveWorld-Set — Banach-algebra exponential defined through completeness. *)

(** * UpReqBanachExpDef: the exponential element of a Banach algebra as a
    completeness-field witness.

    Mission.  The exponential series of an element is Cauchy
    ([exp_series_cauchy], proved in [UpReqBanachExp]); this file turns the
    Cauchy series into an element via the completeness field (witness
    shape [is_cauchy u -> sigT (fun l : BA => blim u l)]): the element is
    [projT1] of the field witness, its convergence specification [projT2].
    Statements: [bxdef_exp], [bxdef_exp_spec], [bxdef_exp_zero_close].

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp]; the [bcauchy]/[blim]/[bpow]/[bae] families are
      reused without redefinition.

    References.  This development, ConstructiveWorld-Main
      UpReqBanachExpDef.v, the baseline module whose statement names are
      carried over here verbatim.

    Constructivity.  All named statements are carried by [Set]; the
      carriers [blim], [bcauchy], [QltT], [bae] are existing Set-carried
      faces.  Extraction gives [Obj.magic] = 0; [coqchk] reports
      [Axioms: none].  Honestly open: [exp 0 = 1] as a [bae] equation and
      uniqueness of limits need a cancellation field the class does not
      carry; [bxdef_exp_zero_close] is the strongest form here.

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachExpDef.v]
      compiles cleanly (exit 0); the artifact starts with [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 1. The exponential element via the completeness field ================= *)

(* Element and certificate together: the Cauchy partial-sum series is fed to
   the completeness field, which returns the limit element paired with its
   convergence specification — a fielded form of "a Cauchy sequence is an
   element". *)
Definition bxdef_exp_pair (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) :
  sigT (fun l : BA => blim BA bae B (fun n => exp_series_partial BA bae B a n) l) :=
  bcauchy_complete_sig BA bae B (fun n => exp_series_partial BA bae B a n)
    (exp_series_cauchy _ _ B a).

(* The exponential element: the element half ([projT1]) of the witness.
   The defining right-hand side carries the structural recursion
   [exp_series_partial] as an argument, so the extracted code contains the
   partial-sum Fixpoint — the definition is itself an algorithm. *)
Definition bxdef_exp (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) : BA :=
  projT1 (bxdef_exp_pair _ _ B a).

(* Convergence specification: the element is the limit of the partial-sum
   series ([projT2] in one step). *)
Lemma bxdef_exp_spec : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA),
  blim BA bae B (fun n => exp_series_partial BA bae B a n) (bxdef_exp _ _ B a).
Proof.
  intros BA bae B a.
  exact (projT2 (bxdef_exp_pair _ _ B a)).
Qed.

(* Eps/N-unfolded form of the specification, so consumers need not destruct
   the [sigT] witness again. *)
Lemma bxdef_exp_spec_eps : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (eps : Q),
  QltT 0 eps ->
  sigT (fun N : nat => forall n : nat,
    NatLe N n ->
    QltT (@bnorm _ _ B (@bplus _ _ B (exp_series_partial BA bae B a n)
                              (@bopp _ _ B (bxdef_exp _ _ B a)))) eps).
Proof.
  intros BA bae B a eps Heps.
  exact (bxdef_exp_spec _ _ B a eps Heps).
Qed.

(* ================= Section 2. The exponential of zero: partial sums at one ================= *)

(* Zero power tail: [bpow bzero (S k)] is [bae]-equal to [bzero], by
   induction on the equality carrier. *)
Lemma bxdef_bpow_zero_tail : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (k : nat),
  bae (bpow BA bae B (@bzero _ _ B) (Datatypes.S k)) (@bzero _ _ B).
Proof.
  intros BA bae B k. induction k as [| j IHj].
  - change (bpow BA bae B (@bzero _ _ B) (Datatypes.S 0%nat))
      with (@bmult _ _ B (@bone _ _ B) (@bzero _ _ B)).
    exact (@bmult_one_l _ _ B (@bzero _ _ B)).
  - change (bpow BA bae B (@bzero _ _ B) (Datatypes.S (Datatypes.S j)))
      with (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S j)) (@bzero _ _ B)).
    eapply bae_trans.
    { exact (@bmult_wd _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S j)) (@bzero _ _ B)
                        (@bzero _ _ B) (@bzero _ _ B)
                        IHj (@bae_refl _ _ B (@bzero _ _ B))). }
    exact (@bmult_zero _ _ B (@bzero _ _ B)).
Qed.

(* Series term vanishing at zero: [bzero^{S k} * (1/(S k)!)] is [bae]-equal
   to [bzero]. *)
Lemma bxdef_esp_term_zero : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (k : nat) (q : Q),
  bae (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S k)) (@bcoef _ _ B q))
        (@bzero _ _ B).
Proof.
  intros BA bae B k q.
  eapply bae_trans.
  { exact (@bmult_wd _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S k)) (@bcoef _ _ B q)
                      (@bzero _ _ B) (@bcoef _ _ B q)
                      (bxdef_bpow_zero_tail _ _ B k)
                      (@bae_refl _ _ B (@bcoef _ _ B q))). }
  eapply bae_trans.
  { exact (@bcoef_comm _ _ B q (@bzero _ _ B)). }
  exact (@bmult_zero _ _ B (@bcoef _ _ B q)).
Qed.

(* Main zero face: every partial sum of the exponential series at [bzero]
   is [bae]-equal to one. *)
Lemma bxdef_esp_zero_series : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat),
  bae (exp_series_partial BA bae B (@bzero _ _ B) n) (@bone _ _ B).
Proof.
  intros BA bae B n. induction n as [| m IHm].
  - change (exp_series_partial BA bae B (@bzero _ _ B) 0%nat) with (@bone _ _ B).
    exact (@bae_refl _ _ B (@bone _ _ B)).
  - change (exp_series_partial BA bae B (@bzero _ _ B) (Datatypes.S m))
      with (@bplus _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m)
              (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S m))
                        (@bcoef _ _ B (/ q_fact (Datatypes.S m))))).
    eapply bae_trans.
    { exact (@bplus_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) m)
                        (@bmult _ _ B (bpow BA bae B (@bzero _ _ B) (Datatypes.S m))
                                  (@bcoef _ _ B (/ q_fact (Datatypes.S m))))
                        (@bone _ _ B) (@bzero _ _ B)
                        IHm
                        (bxdef_esp_term_zero _ _ B m (/ q_fact (Datatypes.S m)))). }
    exact (@bplus_zero _ _ B (@bone _ _ B)).
Qed.

(* Norm face: the norm of every partial sum at zero is [QeqT]-equal to 1. *)
Lemma bxdef_esp_zero_bnorm : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (n : nat),
  QeqT (@bnorm _ _ B (exp_series_partial BA bae B (@bzero _ _ B) n)) 1%Q.
Proof.
  intros BA bae B n.
  pose proof (@bnorm_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) n) (@bone _ _ B)
             (bxdef_esp_zero_series _ _ B n)) as HW.
  pose proof (@bnorm_one _ _ B) as H1.
  assert (HQ1 : QeqT (@bnorm _ _ B (@bone _ _ B)) 1%Q)
    by (destruct H1; apply qeq_imp_qeqT; apply Qeq_refl).
  apply qeq_imp_qeqT.
  apply (Qeq_trans _ (@bnorm _ _ B (@bone _ _ B))).
  - apply qeqT_imp_qeq. exact HW.
  - apply qeqT_imp_qeq. exact HQ1.
Qed.

(* Limit neighborhood face: one and the exponential of zero have arbitrarily
   close norms.  (The full identity [exp 0 = 1] as a [bae] equation would
   need a cancellation field — arbitrarily small norm implies equality —
   which the algebra class does not carry; see the closing note.) *)
Lemma bxdef_exp_zero_close : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (eps : Q),
  QltT 0 eps ->
  QltT (@bnorm _ _ B (@bplus _ _ B (@bone _ _ B)
                           (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B))))) eps.
Proof.
  intros BA bae B eps Heps.
  destruct (bxdef_exp_spec _ _ B (@bzero _ _ B) eps Heps) as [N HN].
  specialize (HN N (NatLe_lift N N (Nat.le_refl N))).
  pose proof (@bnorm_wd _ _ B
      (@bplus _ _ B (exp_series_partial BA bae B (@bzero _ _ B) N)
                (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B))))
      (@bplus _ _ B (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B))))
      (@bplus_wd _ _ B (exp_series_partial BA bae B (@bzero _ _ B) N)
                  (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))
                  (@bone _ _ B) (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))
                  (bxdef_esp_zero_series _ _ B N)
                  (@bae_refl _ _ B (@bopp _ _ B (bxdef_exp _ _ B (@bzero _ _ B)))))) as HWn.
  exact (QeqT_Qlt_bool_cong _ _ eps HWn HN).
Qed.

(* Closing note on what this interface deliberately does not claim.
   Second, the identity [exp 0 = 1] as a [bae] equation, and third,
   uniqueness of limits (two limits of one series are [bae]-equal), both
   require extending the algebra class with a cancellation field
   (arbitrarily small norm implies equality); extending the interface is an
   upstream design decision and is not attempted here.  The first step of
   the dependency chain — defining the limit through
   [bcauchy_complete_sig] — is supplied by this file. *)
