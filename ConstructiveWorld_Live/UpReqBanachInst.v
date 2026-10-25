(* ConstructiveWorld-Set — The first concrete instance problem for the frozen Banach-algebra class. *)

(** * UpReqBanachInst: instance carriers, walls, and the assembly bridge.

    Mission.  The class [BanachAlg] has no instances; this module lands
    the first instance study.  The obstruction is not completeness but
    the [bnorm] field family: [bnorm_wd] has an [Id]-valued codomain and
    [bnorm_coef] pins the scalar norm to [Qabs].  Three candidate
    carriers are blocked: (a) the [Q] carrier with the [QeqT] equality
    forces the false identity [Id (2#4) (1#2)]; (b) the [Q] carrier
    with Leibniz equality hits the denominator-normalization wall
    [Id (0#16) (0#1)]; (c) the [Real] carrier admits early-term
    perturbation counterexamples to any computable candidate.  The
    module contributes: S1 — the in-class construction of the scalar
    Cauchy sequence [v n = coef (1/(n+1))] for an arbitrary [B] with
    its completeness-forced limit; S2 — machine formalizations of the
    two walls on the implication face; S3 — the 39-field
    [BanachAlgPre] record and the assembly bridge
    ([Pre] + completeness gives a full [BanachAlg], with completeness
    as the single remaining gap).

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
    [S03_QExp], [UpReqBanachExp], [UpReqBanachClassExt],
    [UpReqBanachExpAdd] of this development.

    References.  This development, UpReqBanachExp.v, the baseline
    module in ConstructiveWorld-Main whose statement names are carried
    over here verbatim (statement-face Set-carrier completion).

    Constructivity.  Statements are carried by [Set]; the walls are
    stated on the implication face and never land on a Prop terminal
    face.  Statements extract with [Obj.magic] = 0; [coqchk] reports
    [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachInst.v]
    compiles cleanly (exit 0); the first eight bytes of the artifact
    are [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import Lia.

(* ============================================================ *)
(* S0. Transfer helpers between [Id] and [QeqT]/[Qle] (explicit bridges) *)
(* ============================================================ *)

(* [Id] transports [Qle] one way: [Id x y -> Qle z x -> Qle z y]. *)
Lemma bxin_id_qle_r : forall x y z : Q, Id x y -> Qle z x -> QleT' z y.
Proof. intros x y z H Hle. destruct H. apply Qle_to_QleT'. exact Hle. Qed.

(* [1/p <= 1/r] (antitone in the positive denominator; the integer
   order hypotheses pass through). *)
Lemma bxin_qinv_le : forall p r : positive, 
  (Z.pos r <= Z.pos p)%Z -> QleT' (1#p)%Q (1#r)%Q.
Proof.
  intros p r Hrp.
  assert (H1 : (1 <= Z.pos r)%Z) by lia.
  apply Qle_to_QleT'. unfold Qle. simpl. lia.
Qed.

(* Two-term bound: [p, q >= r >= 1] gives [1/p + 1/q <= 2/r]. *)
Lemma bxin_qsum_bound : forall p q r : positive, 
  (Z.pos r <= Z.pos p)%Z -> (Z.pos r <= Z.pos q)%Z ->  
 QleT' (Qplus (1#p)%Q (1#q)%Q) (2#r)%Q.
Proof.
  intros p q r Hp Hq.
  eapply qleT'_trans with (y := (Qplus (1#r)%Q (1#r)%Q)).
  - apply Qle_to_QleT'. apply Qplus_le_compat.
    + apply QleT'_to_Qle. apply (bxin_qinv_le p r Hp).
    + apply QleT'_to_Qle. apply (bxin_qinv_le q r Hq).
  - apply qeq_imp_qle. apply qeq_imp_qeqT. unfold Qeq, Qplus.
    change ((Z.pos r + Z.pos r) * Z.pos r = Z.pos 2 * (Z.pos r * Z.pos r))%Z.
    ring.
Qed.

(* [nat] to [positive] bridge: the integer-level equation, closed by
   [destruct]. *)
Lemma bxin_zpos_succ_nat : forall n : nat,
  @Id Z (Z.pos (Pos.of_succ_nat n)) (Z.succ (Z.of_nat n)).
Proof.
  intro n.
  assert (E : Z.pos (Pos.of_succ_nat n) = Z.succ (Z.of_nat n)) by lia.
  exact (match E in (_ = y) return @Id Z (Z.pos (Pos.of_succ_nat n)) y
         with eq_refl => id_refl end).
Qed.

(* ============================================================ *)
(* S1. The in-class construction: the scalar Cauchy sequence of an
   arbitrary [BanachAlg] and its completeness-forced limit

   Only the class fields [bnorm_plus]/[bnorm_opp]/[bnorm_coef] plus
   rational arithmetic are used; the first non-generic concrete Cauchy
   witness is [v n := coef (1/(n+1))]. *)
(* ============================================================ *)

Lemma bxin_scalar_seq_cauchy : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  forall eps : Q, QltT 0 eps ->
    sigT (fun N : nat => forall m n : nat,
      NatLe N m -> NatLe N n ->
      QltT (@bnorm _ _ B
        (@bplus _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat m))%Q)
                  (@bopp _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat n))%Q)))) eps).
Proof.
  intros BA bae B eps Heps.
  (* Archimedean step: [0 < eps = a#b] yields the bound [L := 4b]. *)
  destruct eps as [a b].
  assert (Hlt0 : Qlt 0 (a#b)%Q) by (apply QltT_to_Qlt; exact Heps).
  unfold Qlt in Hlt0. simpl in Hlt0.
  (* [Hlt0 : (0 < a * Z.pos 1)%Z]. *)
  assert (Hb1 : (1 <= Z.pos b)%Z) by lia.
  assert (Ha1 : (1 <= a)%Z).
  { assert (E : (a * Z.pos 1 = a)%Z) by ring. rewrite E in Hlt0. lia. }
  assert (Hmul : Z.pos (4 * b)%positive = (Z.pos 4 * Z.pos b)%Z) by lia.
  assert (HmL : (2 * Z.pos b < a * Z.pos (4 * b)%positive)%Z).
  { rewrite Hmul. nia. }
  exists (Z.to_nat (Z.pos (4 * b)%positive)).
  intros m n Hm Hn.
  assert (Hmle : (Z.to_nat (Z.pos (4 * b)%positive) <= m)%nat)
    by (apply (NatLe_drop _ _ Hm)).
  assert (Hnle : (Z.to_nat (Z.pos (4 * b)%positive) <= n)%nat)
    by (apply (NatLe_drop _ _ Hn)).
  assert (HmZ : (Z.pos (4 * b)%positive <= Z.of_nat m)%Z) by lia.
  assert (HnZ : (Z.pos (4 * b)%positive <= Z.of_nat n)%Z) by lia.
  assert (HpLm : (Z.pos (4 * b)%positive <= Z.pos (Pos.of_succ_nat m))%Z).
  { rewrite bxin_zpos_succ_nat. lia. }
  assert (HpLn : (Z.pos (4 * b)%positive <= Z.pos (Pos.of_succ_nat n))%Z).
  { rewrite bxin_zpos_succ_nat. lia. }
  (* Rational chain: [norm(v_m - v_n) <= |1/pm| + |1/pn| <= 2/(4b) <
     a#b]. *)
  assert (Hle : Qle
    (@bnorm _ _ B (@bplus _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat m))%Q)
                        (@bopp _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat n))%Q))))
    (Qplus (1#(Pos.of_succ_nat m)%Q) (1#(Pos.of_succ_nat n)%Q))).
  { assert (HQsum : (@bnorm _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat m))%Q)
                     + @bnorm _ _ B (@bopp _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat n))%Q)))%Q
                    == (Qabs (1#(Pos.of_succ_nat m)%Q)
                        + Qabs (1#(Pos.of_succ_nat n)%Q))%Q).
    { apply Qplus_comp.
      - apply qeqT_imp_qeq. apply bnorm_coef_qeq.
      - rewrite (@bnorm_opp _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat n))%Q)).
        apply qeqT_imp_qeq. apply bnorm_coef_qeq. }
    eapply Qle_trans with
      (y := (@bnorm _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat m))%Q)
              + @bnorm _ _ B (@bopp _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat n))%Q)))%Q).
    - (* Subadditivity of [bnorm_plus]. *)
      apply QleT'_to_Qle. apply bnorm_plus.
    - (* Re-basing on [Qeq]. *)
      apply QleT'_to_Qle. apply qeq_le. apply qeq_imp_qeqT. exact HQsum. }
  apply Qlt_to_QltT.
  eapply Qle_lt_trans with (y := (2#(4 * b)%positive)%Q).
  - eapply Qle_trans with (y := (Qplus (1#(Pos.of_succ_nat m)%Q) (1#(Pos.of_succ_nat n)%Q))).
    + exact Hle.
    + apply QleT'_to_Qle.
      exact (bxin_qsum_bound (Pos.of_succ_nat m) (Pos.of_succ_nat n)
                             (4 * b)%positive HpLm HpLn).
  - exact HmL.
Qed.

(* The completeness field forces a limit element: any (future)
   instance contains the limit of the 1/n sequence — the machine form
   of completeness forcing a nonempty carrier. *)
Lemma bxin_scalar_limit_exists : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  sigT (fun l : BA =>
    forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall n : nat,
        NatLe N n ->
        QltT (@bnorm _ _ B (@bplus _ _ B (@bcoef _ _ B (1#(Pos.of_succ_nat n))%Q)
                                 (@bopp _ _ B l))) eps)).
Proof.
  intros BA bae B.
  apply (@bcauchy_complete _ _ B (fun n => @bcoef _ _ B (1#(Pos.of_succ_nat n))%Q)).
  intros eps Heps.
  exact (bxin_scalar_seq_cauchy _ _ B eps Heps).
Qed.

(* Scalar-norm pinning test: [bnorm_coef] pins the norm of [coef q]
   pointwise to [Qabs q]; at [q := 1/2] the pin is [1#2], contradicting
   any discrete norm value. *)
Lemma bxin_bnorm_coef_pin : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (q : Q),
  QeqT (@bnorm _ _ B (@bcoef _ _ B q)) (Qabs q).
Proof. intros BA bae B q. apply bnorm_coef. Qed.

(* Smoke test on the identity face: [coef 1] and [bone] agree in-class. *)
Lemma bxin_bone_is_one : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae),
  bae (@bcoef _ _ B 1%Q) (@bone _ _ B).
Proof. intros BA bae B. apply bcoef_one. Qed.

(* ============================================================ *)
(* S2. Machine formalization of the two walls (implication face,
   Set-typed conclusions throughout) *)
(* ============================================================ *)

(* [2#4 == 1#2] holds at the [QeqT] level (cross-multiplication
   [4 = 4], closed by the comparison computation). *)
Lemma bxin_qeqT_quarter_half : QeqT (2#4)%Q (1#2)%Q.
Proof. unfold QeqT. reflexivity. Qed.

(* Wall one ([QeqT] carrier): [bnorm_wd] (with its [Id] codomain) and
   [bnorm_coef] jointly force the false identity [Id (2#4) (1#2)] —
   injecting through [Qnum]/[QDen] gives a [2 = 1]-type contradiction.
   Any model over [Q] whose equality is [QeqT] cannot satisfy the
   norm-field family. *)
Lemma bxin_Q_bnorm_wall : forall (bn : Q -> Q),
  (forall a b : Q, QeqT a b -> Id (bn a) (bn b)) ->
  (forall q : Q, Id (bn q) (Qabs q)) ->
  Id (2#4)%Q (1#2)%Q.
Proof.
  intros bn Hwd Hpin.
  pose proof (Hwd (2#4)%Q (1#2)%Q bxin_qeqT_quarter_half) as H1.
  pose proof (Hpin (2#4)%Q) as H2.
  pose proof (Hpin (1#2)%Q) as H3.
  exact (id_trans (id_trans (id_sym H2) H1) H3).
Qed.

(* Wall two (Leibniz carrier): the [bplus_opp] field forces a
   denominator-normalization false identity.  Rational addition does
   not normalize: [2#4 + -(2#4) = 0#16] while [bzero = 0#1], and
   [Id (0#16) (0#1)] is not derivable — the denominator positions 16
   versus 1 are the wall. *)
Definition bxin_Q_zero_quarter : Q := Qplus (2#4)%Q (Qopp (2#4)%Q).

Lemma bxin_Q_leibniz_opp_wall :
  Id bxin_Q_zero_quarter (0#1)%Q ->
  Id (QDen bxin_Q_zero_quarter) (QDen (0#1)%Q).
Proof. intros H. exact (id_cong (fun q : Q => QDen q) H). Qed.

(* ============================================================ *)
(* S3. The [BanachAlgPre] record and the assembly bridge

   The field list mirrors [BanachAlg] verbatim except for
   [bcauchy_complete]; the assembly bridge proves that a [Pre]
   structure plus completeness is a full [BanachAlg] — completeness is
   the machine-checked single gap. *)
(* ============================================================ *)

Class bxin_BanachAlgPre := {
  bxin_BA : Set;
  bxin_bae : bxin_BA -> bxin_BA -> Set;
  bxin_bae_refl   : forall a : bxin_BA, bxin_bae a a;
  bxin_bae_sym    : forall a b : bxin_BA, bxin_bae a b -> bxin_bae b a;
  bxin_bae_trans  : forall a b c : bxin_BA,
    bxin_bae a b -> bxin_bae b c -> bxin_bae a c;
  bxin_bzero : bxin_BA;
  bxin_bone : bxin_BA;
  bxin_bplus : bxin_BA -> bxin_BA -> bxin_BA;
  bxin_bmult : bxin_BA -> bxin_BA -> bxin_BA;
  bxin_bopp : bxin_BA -> bxin_BA;
  bxin_bcoef : Q -> bxin_BA;
  bxin_bnorm : bxin_BA -> Q;
  bxin_bplus_assoc : forall a b c : bxin_BA,
    bxin_bae (bxin_bplus a (bxin_bplus b c)) (bxin_bplus (bxin_bplus a b) c);
  bxin_bplus_comm  : forall a b : bxin_BA,
    bxin_bae (bxin_bplus a b) (bxin_bplus b a);
  bxin_bplus_zero  : forall a : bxin_BA, bxin_bae (bxin_bplus a bxin_bzero) a;
  bxin_bplus_opp   : forall a : bxin_BA,
    bxin_bae (bxin_bplus a (bxin_bopp a)) bxin_bzero;
  bxin_bmult_assoc : forall a b c : bxin_BA,
    bxin_bae (bxin_bmult a (bxin_bmult b c)) (bxin_bmult (bxin_bmult a b) c);
  bxin_bmult_one_l : forall a : bxin_BA, bxin_bae (bxin_bmult bxin_bone a) a;
  bxin_bmult_one_r : forall a : bxin_BA, bxin_bae (bxin_bmult a bxin_bone) a;
  bxin_bdistrib_l  : forall a b c : bxin_BA,
    bxin_bae (bxin_bmult a (bxin_bplus b c))
             (bxin_bplus (bxin_bmult a b) (bxin_bmult a c));
  bxin_bdistrib_r  : forall a b c : bxin_BA,
    bxin_bae (bxin_bmult (bxin_bplus a b) c)
             (bxin_bplus (bxin_bmult a c) (bxin_bmult b c));
  bxin_bmult_zero  : forall a : bxin_BA,
    bxin_bae (bxin_bmult a bxin_bzero) bxin_bzero;
  bxin_bplus_wd : forall a b c d : bxin_BA,
    bxin_bae a c -> bxin_bae b d -> bxin_bae (bxin_bplus a b) (bxin_bplus c d);
  bxin_bmult_wd : forall a b c d : bxin_BA,
    bxin_bae a c -> bxin_bae b d -> bxin_bae (bxin_bmult a b) (bxin_bmult c d);
  bxin_bopp_wd  : forall a b : bxin_BA,
    bxin_bae a b -> bxin_bae (bxin_bopp a) (bxin_bopp b);
  bxin_bnorm_wd : forall a b : bxin_BA,
    bxin_bae a b -> QeqT (bxin_bnorm a) (bxin_bnorm b);
  bxin_bcoef_zero : bxin_bae (bxin_bcoef 0%Q) bxin_bzero;
  bxin_bcoef_one  : bxin_bae (bxin_bcoef 1%Q) bxin_bone;
  bxin_bcoef_mult : forall q r : Q,
    bxin_bae (bxin_bcoef (q * r)%Q) (bxin_bmult (bxin_bcoef q) (bxin_bcoef r));
  bxin_bcoef_comm : forall (q : Q) (a : bxin_BA),
    bxin_bae (bxin_bmult a (bxin_bcoef q)) (bxin_bmult (bxin_bcoef q) a);
  (* The dual expansion of the Pre record by the two BCE fields
     (37 fields to 39). *)
  bxin_bcoef_plus : forall q r : Q,
    bxin_bae (bxin_bplus (bxin_bcoef q) (bxin_bcoef r)) (bxin_bcoef (q + r)%Q);
  bxin_bcoef_wd : forall q r : Q, q == r -> bxin_bae (bxin_bcoef q) (bxin_bcoef r);
  bxin_bnorm_zero : Id (bxin_bnorm bxin_bzero) 0%Q;
  bxin_bnorm_one  : Id (bxin_bnorm bxin_bone) 1%Q;
  bxin_bnorm_opp  : forall a : bxin_BA, Id (bxin_bnorm (bxin_bopp a)) (bxin_bnorm a);
  bxin_bnorm_pos  : forall a : bxin_BA, QleT' 0 (bxin_bnorm a);
  bxin_bnorm_plus : forall a b : bxin_BA,
    QleT' (bxin_bnorm (bxin_bplus a b)) (bxin_bnorm a + bxin_bnorm b)%Q;
  bxin_bnorm_mult : forall a b : bxin_BA,
    QleT' (bxin_bnorm (bxin_bmult a b)) (bxin_bnorm a * bxin_bnorm b)%Q;
  bxin_bnorm_coef : forall q : Q, QeqT (bxin_bnorm (bxin_bcoef q)) (Qabs q);
}.

(* The completeness statement over [Pre], mirroring the class field. *)
Definition bxin_pre_complete (p : bxin_BanachAlgPre) : Set :=
  forall (u : nat -> (@bxin_BA p)),
    (forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall m n : nat,
        NatLe N m -> NatLe N n ->
        QltT (@bxin_bnorm p
          (@bxin_bplus p (u m) (@bxin_bopp p (u n)))) eps)) ->
    sigT (fun l : (@bxin_BA p) => forall eps : Q, QltT 0 eps ->
      sigT (fun N : nat => forall n : nat,
        NatLe N n ->
        QltT (@bxin_bnorm p
          (@bxin_bplus p (u n) (@bxin_bopp p l))) eps)).

(* Assembly bridge: a [Pre] structure plus completeness is a full
   [BanachAlg]; apart from the completeness field there are no gaps. *)
Definition bxin_BanachAlg_of_pre (p : bxin_BanachAlgPre)
  (Hc : bxin_pre_complete p) : BanachAlg (@bxin_BA p) (@bxin_bae p).
Proof.
  exact {|
           bae_refl := @bxin_bae_refl p;
           bae_sym := @bxin_bae_sym p;
           bae_trans := @bxin_bae_trans p;
           bzero := @bxin_bzero p;
           bone := @bxin_bone p;
           bplus := @bxin_bplus p;
           bmult := @bxin_bmult p;
           bopp := @bxin_bopp p;
           bcoef := @bxin_bcoef p;
           bnorm := @bxin_bnorm p;
           bplus_assoc := @bxin_bplus_assoc p;
           bplus_comm := @bxin_bplus_comm p;
           bplus_zero := @bxin_bplus_zero p;
           bplus_opp := @bxin_bplus_opp p;
           bmult_assoc := @bxin_bmult_assoc p;
           bmult_one_l := @bxin_bmult_one_l p;
           bmult_one_r := @bxin_bmult_one_r p;
           bdistrib_l := @bxin_bdistrib_l p;
           bdistrib_r := @bxin_bdistrib_r p;
           bmult_zero := @bxin_bmult_zero p;
           bplus_wd := @bxin_bplus_wd p;
           bmult_wd := @bxin_bmult_wd p;
           bopp_wd := @bxin_bopp_wd p;
           bnorm_wd := @bxin_bnorm_wd p;
           bcoef_zero := @bxin_bcoef_zero p;
           bcoef_one := @bxin_bcoef_one p;
           bcoef_mult := @bxin_bcoef_mult p;
           bcoef_comm := @bxin_bcoef_comm p;
           bcoef_plus := @bxin_bcoef_plus p;
           bcoef_wd := fun q r Hq => @bxin_bcoef_wd p q r (qeqT_imp_qeq q r Hq);
           bnorm_zero := @bxin_bnorm_zero p;
           bnorm_one := @bxin_bnorm_one p;
           bnorm_opp := @bxin_bnorm_opp p;
           bnorm_pos := @bxin_bnorm_pos p;
           bnorm_plus := @bxin_bnorm_plus p;
           bnorm_mult := @bxin_bnorm_mult p;
           bnorm_coef := @bxin_bnorm_coef p;
           bcauchy_complete := Hc |}.
Defined.

(* Smoke test of the assembly: the assembled structure satisfies the
   in-class identity law. *)
Lemma bxin_asmoke_bone_is_one : forall (p : bxin_BanachAlgPre)
  (Hc : bxin_pre_complete p),
  @bxin_bae p
       (@bcoef _ _ (bxin_BanachAlg_of_pre p Hc) 1%Q)
       (@bone _ _ (bxin_BanachAlg_of_pre p Hc)).
Proof.
  intros p Hc. apply bxin_bone_is_one.
Qed.

(* ============================================================ *)
(* Extraction audit *)
(* ============================================================ *)
From Stdlib Require Import Extraction.
Separate Extraction bxin_scalar_seq_cauchy bxin_scalar_limit_exists
  bxin_bnorm_coef_pin bxin_bone_is_one bxin_Q_bnorm_wall
  bxin_Q_leibniz_opp_wall bxin_BanachAlg_of_pre.
