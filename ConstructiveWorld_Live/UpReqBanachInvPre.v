(* ConstructiveWorld-Set — Banach exponential inverse: the special case [: x = a + (-a)]. *)

(** * UpReqBanachInvPre: vanishing powers and the product pairing identity
    for [: a + (-a)].

    Mission.  The inverse law [: e^a * e^{-a} = e^0 = 1] needs, in general,
    the binomial identity for powers of a sum; this file attacks the special
    case [: x = a + (-a)]: such [x] satisfies [bplus_opp], so [: x^n]
    vanishes for every [: n >= 1] with no binomial coefficients at all.
    Statements: the engine supplements [binv_bmult_zero_l], [binv_bpow_wd],
    [binv_esp_wd]; the power face [binv_bpow_opp_add] with its certificate
    [binv_bpow_opp_add_mesh] and the main anchor [binv_esp_opp_add]; the
    pairing identity [binv_pair]; and the alternating diagonal family.

    Dependencies.  Stdlib [QArith.QArith], [QArith.Qabs], [Arith.Arith],
      [Lia].  Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [UpReqBanachExp], [UpReqBanachProd], [UpReqBanachExpBasic]; the class
      [BanachAlg] and the sum engine [bsum] with [esp_as_bsum],
      [esp_prod_square], [bsum_rot] are reused without redefinition.

    References.  This development, ConstructiveWorld-Main
      UpReqBanachInvPre.v, whose statement names are carried over verbatim.

    Constructivity.  All named statements are carried by [Set]
      ([bae], [Id], [sigT], [QltT]); the only Prop occurrences are inner
      rational-equality steps inside proofs.  Extraction gives
      [Obj.magic] = 0; [coqchk] reports [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpReqBanachInvPre.v]
      compiles cleanly (exit 0); the artifact starts with
      [436f7121 00015ff4]. *)

Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import UpReqBanachExp.
Require Import UpReqBanachProd.
Require Import UpReqBanachExpBasic.
From Stdlib Require Import QArith.QArith QArith.Qabs Arith.Arith.
From Stdlib Require Import Lia.

(* ================= Section 0. Engine supplements: left annihilation and transport ================= *)

(* Left annihilation: [bzero * x] equals [bzero].  The class field
   [bmult_zero] only annihilates on the right; in a non-commutative algebra
   the proof detours through the scalar image of [0], swapping sides with
   [bcoef_comm] and closing with [bcoef_zero]. *)
Lemma binv_bmult_zero_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B (@bzero _ _ B) x) (@bzero _ _ B).
Proof.
  intros BA bae B x.
  eapply bae_trans.
  - (* [bzero * x] read as [(bcoef 0) * x]. *)
    apply (@bmult_wd _ _ B (@bzero _ _ B) x (@bcoef _ _ B 0%Q) x).
    + apply (@bae_sym _ _ B). exact (@bcoef_zero _ _ B).
    + apply (@bae_refl _ _ B).
  - (* [(bcoef 0) * x = x * (bcoef 0) = x * bzero = bzero]. *)
    apply (@bae_trans _ _ B _ (@bmult _ _ B x (@bcoef _ _ B 0%Q)) _).
    + apply (@bae_sym _ _ B). exact (@bcoef_comm _ _ B 0%Q x).
    + apply (@bae_trans _ _ B _ (@bmult _ _ B x (@bzero _ _ B)) _).
      * apply (@bmult_wd _ _ B x (@bcoef _ _ B 0%Q) x (@bzero _ _ B)).
        -- apply (@bae_refl _ _ B).
        -- exact (@bcoef_zero _ _ B).
      * exact (@bmult_zero _ _ B x).
Qed.

(* Transport of [bae] through powers, by induction and [bmult_wd]. *)
Lemma binv_bpow_wd : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y : BA),
  bae x y -> forall n : nat, bae (bpow BA bae B x n) (bpow BA bae B y n).
Proof.
  intros BA bae B x y Hxy n. induction n as [| m IH].
  - apply (@bae_refl _ _ B).
  - change (bpow BA bae B x (Datatypes.S m)) with (@bmult _ _ B (bpow BA bae B x m) x).
    change (bpow BA bae B y (Datatypes.S m)) with (@bmult _ _ B (bpow BA bae B y m) y).
    apply (@bmult_wd _ _ B).
    + exact IH.
    + exact Hxy.
Qed.

(* Transport of [bae] through exponential partial sums, level by level by
   [bplus_wd] and [bmult_wd]. *)
Lemma binv_esp_wd : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y : BA),
  bae x y -> forall n : nat,
  bae (exp_series_partial BA bae B x n) (exp_series_partial BA bae B y n).
Proof.
  intros BA bae B x y Hxy n. induction n as [| m IH].
  - apply (@bae_refl _ _ B).
  - change (exp_series_partial BA bae B x (Datatypes.S m))
      with (@bplus _ _ B (exp_series_partial BA bae B x m)
              (@bmult _ _ B (bpow BA bae B x (Datatypes.S m))
                        (@bcoef _ _ B (/ q_fact (Datatypes.S m))))).
    change (exp_series_partial BA bae B y (Datatypes.S m))
      with (@bplus _ _ B (exp_series_partial BA bae B y m)
              (@bmult _ _ B (bpow BA bae B y (Datatypes.S m))
                        (@bcoef _ _ B (/ q_fact (Datatypes.S m))))).
    apply (@bplus_wd _ _ B).
    + exact IH.
    + apply (@bmult_wd _ _ B).
      * exact (binv_bpow_wd _ _ B x y Hxy (Datatypes.S m)).
      * apply (@bae_refl _ _ B).
Qed.

(* ================= Section 1. The power [: (a + (-a))^n] vanishes for [: n >= 1] ================= *)

(* Induction on [: n] along the [bae] carrier, with the same skeleton as
   [bxb_bpow_zero] and left annihilation from Section 0.
   Base [: n = 1]: [bone * (a + (-a))] reduces to [a + (-a)], annihilated by
   [bplus_opp].  Step [: n = S (S j)]: the induction premise already
   annihilates the leading factor, and left annihilation closes — each step
   retires one [bplus_opp] factor. *)
Lemma binv_bpow_opp_add : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (n : nat),
  (1 <= n)%nat -> bae (bpow BA bae B (@bplus _ _ B a (@bopp _ _ B a)) n) (@bzero _ _ B).
Proof.
  intros BA bae B a n Hn. destruct n as [| m].
  - exfalso. lia.
  - induction m as [| j IH].
    + (* Base [: n = 1]: [bone * (a + (-a))] to [a + (-a)] to [bzero]. *)
      change (bpow BA bae B (@bplus _ _ B a (@bopp _ _ B a)) (Datatypes.S 0%nat))
        with (@bmult _ _ B (@bone _ _ B) (@bplus _ _ B a (@bopp _ _ B a))).
      apply (@bae_trans _ _ B _ (@bplus _ _ B a (@bopp _ _ B a)) _).
      * exact (@bmult_one_l _ _ B (@bplus _ _ B a (@bopp _ _ B a))).
      * exact (@bplus_opp _ _ B a).
    + (* Step [: n = S (S j)]: the premise retires the first factor; left
         annihilation closes. *)
      assert (Hj : (1 <= Datatypes.S j)%nat) by lia.
      change (bpow BA bae B (@bplus _ _ B a (@bopp _ _ B a)) (Datatypes.S (Datatypes.S j)))
        with (@bmult _ _ B (bpow BA bae B (@bplus _ _ B a (@bopp _ _ B a)) (Datatypes.S j))
                       (@bplus _ _ B a (@bopp _ _ B a))).
      apply (@bae_trans _ _ B _ (@bmult _ _ B (@bzero _ _ B) (@bplus _ _ B a (@bopp _ _ B a))) _).
      * apply (@bmult_wd _ _ B (bpow BA bae B (@bplus _ _ B a (@bopp _ _ B a)) (Datatypes.S j))
                           (@bplus _ _ B a (@bopp _ _ B a))
                           (@bzero _ _ B) (@bplus _ _ B a (@bopp _ _ B a))).
        -- exact (IH Hj).
        -- apply (@bae_refl _ _ B).
      * exact (binv_bmult_zero_l _ _ B (@bplus _ _ B a (@bopp _ _ B a))).
Qed.

(* Matching certificate: the vanishing powers of Section 1 and the zero
   powers of [UpReqBanachExpBasic] agree at every [: n] by transport with
   [bpow_wd] — either side may serve as the power face of [: e^0]. *)
Lemma binv_bpow_opp_add_mesh : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (n : nat),
  (1 <= n)%nat ->
  bae (bpow BA bae B (@bplus _ _ B a (@bopp _ _ B a)) n) (bpow BA bae B (@bzero _ _ B) n).
Proof.
  intros BA bae B a n Hn.
  exact (binv_bpow_wd _ _ B (@bplus _ _ B a (@bopp _ _ B a)) (@bzero _ _ B)
           (@bplus_opp _ _ B a) n).
Qed.

(* Main anchor of Section 1: every partial sum of the exponential series of
   [: a + (-a)] equals [bone] — the all-partial-sums face of [: e^0 = 1] at
   the Banach level, with the limit coming for free, joining
   [bxb_series_zero]. *)
Lemma binv_esp_opp_add : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (n : nat),
  bae (exp_series_partial BA bae B (@bplus _ _ B a (@bopp _ _ B a)) n) (@bone _ _ B).
Proof.
  intros BA bae B a n.
  apply (@bae_trans _ _ B _ (exp_series_partial BA bae B (@bzero _ _ B) n) _).
  - exact (binv_esp_wd _ _ B (@bplus _ _ B a (@bopp _ _ B a)) (@bzero _ _ B)
             (@bplus_opp _ _ B a) n).
  - exact (bxb_series_zero _ _ B n).
Qed.

(* ================= Section 2. The partial-sum product pairing identity ================= *)

(* Row folding: row [: j] of the Cauchy square equals [: c_j * esp m b], by
   factoring out [: c_j = a^j * coef(1/j!)] with [bsum_mult_l] and reading
   the inner sum back as a partial sum with [esp_as_bsum]. *)
Lemma binv_row_fold : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a b : BA) (m j : nat),
  bae (bsum _ _ B (Datatypes.S m)
             (fun i : nat =>
                @bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
                         (@bmult _ _ B (bpow BA bae B b i) (@bcoef _ _ B (/ q_fact i)))))
         (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
                  (exp_series_partial BA bae B b m)).
Proof.
  intros BA bae B a b m j.
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
             (bsum _ _ B (Datatypes.S m)
                (fun i : nat =>
                   @bmult _ _ B (bpow BA bae B b i) (@bcoef _ _ B (/ q_fact i))))) _).
  - exact (bsum_mult_l _ _ B (Datatypes.S m)
             (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
             (fun i : nat => @bmult _ _ B (bpow BA bae B b i) (@bcoef _ _ B (/ q_fact i)))).
  - apply (@bmult_wd _ _ B).
    + apply (@bae_refl _ _ B).
    + apply (@bae_sym _ _ B). exact (esp_as_bsum _ _ B b m).
Qed.

(* The leading row ([: j = 0]) collapses to [esp m b]:
   [: c_0 = bone * coef(1/0!) = bone]. *)
Lemma binv_row_zero : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (b : BA) (m : nat),
  bae (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B (/ q_fact 0%nat)))
                   (exp_series_partial BA bae B b m))
         (exp_series_partial BA bae B b m).
Proof.
  intros BA bae B b m.
  assert (Hq0 : (/ q_fact 0%nat)%Q = 1%Q) by reflexivity.
  apply (@bae_trans _ _ B _ (@bmult _ _ B (@bone _ _ B) (exp_series_partial BA bae B b m)) _).
  - apply (@bmult_wd _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B (/ q_fact 0%nat)))
                       (exp_series_partial BA bae B b m)
                       (@bone _ _ B) (exp_series_partial BA bae B b m)).
    + rewrite Hq0.
      apply (@bae_trans _ _ B _ (@bcoef _ _ B 1%Q) _).
      * exact (@bmult_one_l _ _ B (@bcoef _ _ B 1%Q)).
      * exact (@bcoef_one _ _ B).
    + apply (@bae_refl _ _ B).
  - exact (@bmult_one_l _ _ B (exp_series_partial BA bae B b m)).
Qed.

(* Main statement of Section 2: [: esp m a * esp m (-a)] equals
   [: esp m (-a)] plus the paired remainder sum over [: k < m].  The Cauchy
   square is pulled out row by row ([esp_prod_square]); the leading row is
   the whole second factor, and the remaining rows are the paired remainder
   ([bsum_rot] lifts it).  Joined with the main anchor of Section 1 — the
   second-factor series is constantly one — a general binomial theorem that
   retires the remainder would complete the inverse law. *)
Lemma binv_pair : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (m : nat),
  bae (@bmult _ _ B (exp_series_partial BA bae B a m)
                   (exp_series_partial BA bae B (@bopp _ _ B a) m))
         (@bplus _ _ B (exp_series_partial BA bae B (@bopp _ _ B a) m)
                   (bsum _ _ B m
                      (fun k : nat =>
                         @bmult _ _ B (@bmult _ _ B (bpow BA bae B a (Datatypes.S k))
                                          (@bcoef _ _ B (/ q_fact (Datatypes.S k))))
                                  (exp_series_partial BA bae B (@bopp _ _ B a) m)))).
Proof.
  intros BA bae B a m.
  apply (@bae_trans _ _ B _
    (bsum _ _ B (Datatypes.S m)
       (fun j : nat =>
          bsum _ _ B (Datatypes.S m)
            (fun i : nat =>
               @bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
                        (@bmult _ _ B (bpow BA bae B (@bopp _ _ B a) i)
                                  (@bcoef _ _ B (/ q_fact i)))))) _).
  - (* The Cauchy square, directly from [esp_prod_square]. *)
    exact (esp_prod_square _ _ B a (@bopp _ _ B a) m).
  - (* Row folding, lift of the leading row by rotation, collapse of the
       leading row. *)
    apply (@bae_trans _ _ B _
      (bsum _ _ B (Datatypes.S m)
         (fun j : nat =>
            @bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
                     (exp_series_partial BA bae B (@bopp _ _ B a) m))) _).
    + eapply bsum_ext.
      intros k Hk. exact (binv_row_fold _ _ B a (@bopp _ _ B a) m k).
    + apply (@bae_trans _ _ B _
        (@bplus _ _ B (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bcoef _ _ B (/ q_fact 0%nat)))
                            (exp_series_partial BA bae B (@bopp _ _ B a) m))
                  (bsum _ _ B m
                     (fun k : nat =>
                        @bmult _ _ B (@bmult _ _ B (bpow BA bae B a (Datatypes.S k))
                                         (@bcoef _ _ B (/ q_fact (Datatypes.S k))))
                                 (exp_series_partial BA bae B (@bopp _ _ B a) m)))) _).
      * exact (bsum_rot _ _ B m
            (fun j : nat =>
               @bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (@bcoef _ _ B (/ q_fact j)))
                        (exp_series_partial BA bae B (@bopp _ _ B a) m))).
      * apply (@bplus_wd_l BA bae B _ _ _).
        exact (binv_row_zero _ _ B (@bopp _ _ B a) m).
Qed.

(* ================= Section 3. Toward the alternating diagonal structure ================= *)

(* Left multiplication by an additive inverse flips the sign:
   [(-x) * z] equals [- (x * z)], by right distributivity, left annihilation
   and uniqueness of the additive inverse. *)
Lemma binv_bmult_opp_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x z : BA),
  bae (@bmult _ _ B (@bopp _ _ B x) z) (@bopp _ _ B (@bmult _ _ B x z)).
Proof.
  intros BA bae B x z.
  apply (@bopp_unique BA bae B (@bmult _ _ B (@bopp _ _ B x) z) (@bmult _ _ B x z)).
  apply (@bae_trans _ _ B _ (@bmult _ _ B (@bplus _ _ B (@bopp _ _ B x) x) z) _).
  - apply (@bae_sym _ _ B). exact (@bdistrib_r _ _ B (@bopp _ _ B x) x z).
  - apply (@bae_trans _ _ B _ (@bmult _ _ B (@bzero _ _ B) z) _).
    + apply (@bmult_wd _ _ B (@bplus _ _ B (@bopp _ _ B x) x) z (@bzero _ _ B) z).
      * apply (@bae_trans _ _ B _ (@bplus _ _ B x (@bopp _ _ B x)) _).
        -- exact (@bplus_comm _ _ B (@bopp _ _ B x) x).
        -- exact (@bplus_opp _ _ B x).
      * apply (@bae_refl _ _ B).
    + exact (binv_bmult_zero_l _ _ B z).
Qed.

(* Right multiplication by an additive inverse flips the sign:
   [x * (-x)] equals [- (x * x)], by left distributivity. *)
Lemma binv_mult_opp_r : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B x (@bopp _ _ B x)) (@bopp _ _ B (@bmult _ _ B x x)).
Proof.
  intros BA bae B x.
  apply (@bopp_unique BA bae B (@bmult _ _ B x (@bopp _ _ B x)) (@bmult _ _ B x x)).
  apply (@bae_trans _ _ B _ (@bmult _ _ B x (@bplus _ _ B (@bopp _ _ B x) x)) _).
  - apply (@bae_sym _ _ B). exact (@bdistrib_l _ _ B x (@bopp _ _ B x) x).
  - apply (@bae_trans _ _ B _ (@bmult _ _ B x (@bzero _ _ B)) _).
    + apply (@bmult_wd _ _ B x (@bplus _ _ B (@bopp _ _ B x) x) x (@bzero _ _ B)).
      * apply (@bae_refl _ _ B).
      * apply (@bae_trans _ _ B _ (@bplus _ _ B x (@bopp _ _ B x)) _).
        -- exact (@bplus_comm _ _ B (@bopp _ _ B x) x).
        -- exact (@bplus_opp _ _ B x).
    + exact (@bmult_zero _ _ B x).
Qed.

(* The mirrored form: [(-x) * x] equals [- (x * x)], dual to
   [binv_mult_opp_r]. *)
Lemma binv_mult_opp_l : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B (@bopp _ _ B x) x) (@bopp _ _ B (@bmult _ _ B x x)).
Proof.
  intros BA bae B x.
  apply (@bopp_unique BA bae B (@bmult _ _ B (@bopp _ _ B x) x) (@bmult _ _ B x x)).
  apply (@bae_trans _ _ B _ (@bmult _ _ B (@bplus _ _ B (@bopp _ _ B x) x) x) _).
  - apply (@bae_sym _ _ B). exact (@bdistrib_r _ _ B (@bopp _ _ B x) x x).
  - apply (@bae_trans _ _ B _ (@bmult _ _ B (@bzero _ _ B) x) _).
    + apply (@bmult_wd _ _ B (@bplus _ _ B (@bopp _ _ B x) x) x (@bzero _ _ B) x).
      * apply (@bae_trans _ _ B _ (@bplus _ _ B x (@bopp _ _ B x)) _).
        -- exact (@bplus_comm _ _ B (@bopp _ _ B x) x).
        -- exact (@bplus_opp _ _ B x).
      * apply (@bae_refl _ _ B).
    + exact (binv_bmult_zero_l _ _ B x).
Qed.

(* [: a] and [(-a)] commute: [a * (-a)] equals [(-a) * a], both arms
   equalling [- (a * a)] — the commutation certificate that instantiates
   the power-reordering engine [bpow_comm_r]. *)
Lemma binv_mult_opp_swap : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA),
  bae (@bmult _ _ B a (@bopp _ _ B a)) (@bmult _ _ B (@bopp _ _ B a) a).
Proof.
  intros BA bae B a.
  apply (@bae_trans _ _ B _ (@bopp _ _ B (@bmult _ _ B a a)) _).
  - exact (binv_mult_opp_r _ _ B a).
  - apply (@bae_sym _ _ B). exact (binv_mult_opp_l _ _ B a).
Qed.

(* Product of two inverses: [(-x) * (-x)] equals [x * x]. *)
Lemma binv_bmult_opp_opp : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x : BA),
  bae (@bmult _ _ B (@bopp _ _ B x) (@bopp _ _ B x)) (@bmult _ _ B x x).
Proof.
  intros BA bae B x.
  apply (@bae_trans _ _ B _ (@bopp _ _ B (@bmult _ _ B x (@bopp _ _ B x))) _).
  - exact (binv_bmult_opp_l _ _ B x (@bopp _ _ B x)).
  - apply (@bae_trans _ _ B _ (@bopp _ _ B (@bopp _ _ B (@bmult _ _ B x x))) _).
    + apply (@bopp_wd _ _ B). exact (binv_mult_opp_r _ _ B x).
    + apply (@bae_sym _ _ B).
      exact (@bopp_unique BA bae B (@bmult _ _ B x x) (@bopp _ _ B (@bmult _ _ B x x))
               (@bplus_opp _ _ B (@bmult _ _ B x x))).
Qed.

(* Even-power seed: the square of [(-u)] equals the square of [u] — the
   even-order terms of the alternating structure carry a positive sign. *)
Lemma binv_bpow_opp2 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (u : BA),
  bae (bpow BA bae B (@bopp _ _ B u) (Datatypes.S (Datatypes.S 0%nat)))
         (bpow BA bae B u (Datatypes.S (Datatypes.S 0%nat))).
Proof.
  intros BA bae B u.
  change (bpow BA bae B (@bopp _ _ B u) (Datatypes.S (Datatypes.S 0%nat)))
    with (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bopp _ _ B u)) (@bopp _ _ B u)).
  change (bpow BA bae B u (Datatypes.S (Datatypes.S 0%nat)))
    with (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) u) u).
  apply (@bae_trans _ _ B _ (@bmult _ _ B (@bopp _ _ B u) (@bopp _ _ B u)) _).
  - apply (@bmult_wd _ _ B (@bmult _ _ B (@bone _ _ B) (@bopp _ _ B u)) (@bopp _ _ B u)
                       (@bopp _ _ B u) (@bopp _ _ B u)).
    + exact (@bmult_one_l _ _ B (@bopp _ _ B u)).
    + apply (@bae_refl _ _ B).
  - apply (@bae_trans _ _ B _ (@bmult _ _ B u u) _).
    + exact (binv_bmult_opp_opp _ _ B u).
    + apply (@bae_sym _ _ B).
      apply (@bmult_wd _ _ B (@bmult _ _ B (@bone _ _ B) u) u u u).
      * exact (@bmult_one_l _ _ B u).
      * apply (@bae_refl _ _ B).
Qed.

(* Four-factor rearrangement: [(w * y) * (x * z)] equals
   [(w * x) * (y * z)] given [y * x = x * y] — the multiplicative companion
   of [bplus_swap4], driving the splitting of powers. *)
Lemma binv_bmult_swap4 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (w x y z : BA),
  bae (@bmult _ _ B y x) (@bmult _ _ B x y) ->
  bae (@bmult _ _ B (@bmult _ _ B w y) (@bmult _ _ B x z))
         (@bmult _ _ B (@bmult _ _ B w x) (@bmult _ _ B y z)).
Proof.
  intros BA bae B w x y z Hcomm.
  apply (@bae_trans _ _ B _ (@bmult _ _ B w (@bmult _ _ B y (@bmult _ _ B x z))) _).
  - apply (@bae_sym _ _ B). exact (@bmult_assoc _ _ B w y (@bmult _ _ B x z)).
  - apply (@bae_trans _ _ B _ (@bmult _ _ B w (@bmult _ _ B (@bmult _ _ B y x) z)) _).
    + apply (@bmult_wd _ _ B w (@bmult _ _ B y (@bmult _ _ B x z))
                       w (@bmult _ _ B (@bmult _ _ B y x) z)).
      * apply (@bae_refl _ _ B).
      * exact (@bmult_assoc _ _ B y x z).
    + apply (@bae_trans _ _ B _ (@bmult _ _ B w (@bmult _ _ B x (@bmult _ _ B y z))) _).
      * apply (@bmult_wd _ _ B w (@bmult _ _ B (@bmult _ _ B y x) z)
                         w (@bmult _ _ B x (@bmult _ _ B y z))).
        -- apply (@bae_refl _ _ B).
        -- apply (@bae_trans _ _ B _ (@bmult _ _ B (@bmult _ _ B x y) z) _).
           ++ apply (@bmult_wd _ _ B (@bmult _ _ B y x) z (@bmult _ _ B x y) z).
              ** exact Hcomm.
              ** apply (@bae_refl _ _ B).
           ++ apply (@bae_sym _ _ B). exact (@bmult_assoc _ _ B x y z).
      * exact (@bmult_assoc _ _ B w x (@bmult _ _ B y z)).
Qed.

(* Splitting a product base across powers: [(a * (-a))^k] equals
   [: a^k * (-a)^k], by induction with the four-factor rearrangement; the
   commutation certificate [binv_mult_opp_swap] feeds [bpow_comm_r]. *)
Lemma binv_bpow_split : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (k : nat),
  bae (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) k)
         (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B (@bopp _ _ B a) k)).
Proof.
  intros BA bae B a k. induction k as [| j IH].
  - change (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) 0%nat) with (@bone _ _ B).
    change (@bmult _ _ B (bpow BA bae B a 0%nat) (bpow BA bae B (@bopp _ _ B a) 0%nat))
      with (@bmult _ _ B (@bone _ _ B) (@bone _ _ B)).
    apply (@bae_sym _ _ B). exact (@bmult_one_l _ _ B (@bone _ _ B)).
  - change (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) (Datatypes.S j))
      with (@bmult _ _ B (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) j)
                     (@bmult _ _ B a (@bopp _ _ B a))).
    change (bpow BA bae B a (Datatypes.S j)) with (@bmult _ _ B (bpow BA bae B a j) a).
    change (bpow BA bae B (@bopp _ _ B a) (Datatypes.S j))
      with (@bmult _ _ B (bpow BA bae B (@bopp _ _ B a) j) (@bopp _ _ B a)).
    apply (@bae_trans _ _ B _
      (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a j) (bpow BA bae B (@bopp _ _ B a) j))
                (@bmult _ _ B a (@bopp _ _ B a))) _).
    + apply (@bmult_wd _ _ B (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) j)
                         (@bmult _ _ B a (@bopp _ _ B a))
                         (@bmult _ _ B (bpow BA bae B a j) (bpow BA bae B (@bopp _ _ B a) j))
                         (@bmult _ _ B a (@bopp _ _ B a))).
      * exact IH.
      * apply (@bae_refl _ _ B).
    + exact (binv_bmult_swap4 _ _ B (bpow BA bae B a j) a
                (bpow BA bae B (@bopp _ _ B a) j) (@bopp _ _ B a)
                (bpow_comm_r _ _ B (@bopp _ _ B a) a
                   (@bae_sym _ _ B _ _ (binv_mult_opp_swap _ _ B a)) j)).
Qed.

(* Scalar folding: [(x * cq) * (y * cr)] equals [(x * y) * coef(q * r)],
   swapping through [bcoef_comm] and folding with [bcoef_mult] — the engine
   that merges the two [: 1/k!] coefficients of a diagonal term. *)
Lemma binv_bmult_coef_fold : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (x y : BA) (q r : Q),
  bae (@bmult _ _ B (@bmult _ _ B x (@bcoef _ _ B q)) (@bmult _ _ B y (@bcoef _ _ B r)))
         (@bmult _ _ B (@bmult _ _ B x y) (@bcoef _ _ B (q * r)%Q)).
Proof.
  intros BA bae B x y q r.
  apply (@bae_trans _ _ B _
    (@bmult _ _ B x (@bmult _ _ B (@bcoef _ _ B q) (@bmult _ _ B y (@bcoef _ _ B r)))) _).
  - apply (@bae_sym _ _ B).
    exact (@bmult_assoc _ _ B x (@bcoef _ _ B q) (@bmult _ _ B y (@bcoef _ _ B r))).
  - apply (@bae_trans _ _ B _
      (@bmult _ _ B x (@bmult _ _ B (@bmult _ _ B y (@bcoef _ _ B q)) (@bcoef _ _ B r))) _).
    + (* [cq * (y * cr)] equals [(cq * y) * cr] and hence [(y * cq) * cr]. *)
      apply (@bmult_wd _ _ B x (@bmult _ _ B (@bcoef _ _ B q) (@bmult _ _ B y (@bcoef _ _ B r)))
                       x (@bmult _ _ B (@bmult _ _ B y (@bcoef _ _ B q)) (@bcoef _ _ B r))).
      * apply (@bae_refl _ _ B).
      * apply (@bae_trans _ _ B _
          (@bmult _ _ B (@bmult _ _ B (@bcoef _ _ B q) y) (@bcoef _ _ B r)) _).
        -- exact (@bmult_assoc _ _ B (@bcoef _ _ B q) y (@bcoef _ _ B r)).
        -- apply (@bmult_wd _ _ B (@bmult _ _ B (@bcoef _ _ B q) y) (@bcoef _ _ B r)
                             (@bmult _ _ B y (@bcoef _ _ B q)) (@bcoef _ _ B r)).
           ++ apply (@bae_sym _ _ B). exact (@bcoef_comm _ _ B q y).
           ++ apply (@bae_refl _ _ B).
    + (* [x * (y * (cq * cr))] equals [x * (y * coef(q r))] and hence
         [(x * y) * coef(q r)]. *)
      apply (@bae_trans _ _ B _
        (@bmult _ _ B x (@bmult _ _ B y (@bcoef _ _ B (q * r)%Q))) _).
      * apply (@bae_trans _ _ B _
          (@bmult _ _ B x (@bmult _ _ B y (@bmult _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)))) _).
        -- apply (@bmult_wd _ _ B x (@bmult _ _ B (@bmult _ _ B y (@bcoef _ _ B q)) (@bcoef _ _ B r))
                             x (@bmult _ _ B y (@bmult _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)))).
           ++ apply (@bae_refl _ _ B).
           ++ apply (@bae_sym _ _ B).
              exact (@bmult_assoc _ _ B y (@bcoef _ _ B q) (@bcoef _ _ B r)).
        -- apply (@bmult_wd _ _ B x (@bmult _ _ B y (@bmult _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r)))
                             x (@bmult _ _ B y (@bcoef _ _ B (q * r)%Q))).
           ++ apply (@bae_refl _ _ B).
           ++ apply (@bmult_wd _ _ B y (@bmult _ _ B (@bcoef _ _ B q) (@bcoef _ _ B r))
                                y (@bcoef _ _ B (q * r)%Q)).
              ** apply (@bae_refl _ _ B).
              ** apply (@bae_sym _ _ B). exact (@bcoef_mult _ _ B q r).
      * exact (@bmult_assoc _ _ B x y (@bcoef _ _ B (q * r)%Q)).
Qed.

(* The diagonal term: [: D_k = (a^k / k!) * ((-a)^k / k!)]. *)
Definition binv_diag_term (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (k : nat) : BA :=
  @bmult _ _ B (@bmult _ _ B (bpow BA bae B a k) (@bcoef _ _ B (/ q_fact k)))
           (@bmult _ _ B (bpow BA bae B (@bopp _ _ B a) k) (@bcoef _ _ B (/ q_fact k))).

(* Alternating folding of a diagonal term: [: D_k] equals
   [: (a * (-a))^k * coef((1/k!) * (1/k!))] — the sign carrier is absorbed
   into the power base [: a * (-a)] (which equals [- (a * a)], whose even
   powers are [: a^{2k}] by the seed above and whose odd powers are
   [- (a^{2k})]), while the rational coefficient [: (1/k!)^2] stays
   positive — the starting point of the alternating sum
   [: sum of (-1)^k a^{2k} / (k!)^2]. *)
Lemma binv_diag_term_pair : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA) (k : nat),
  bae (binv_diag_term _ _ B a k)
         (@bmult _ _ B (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) k)
                   (@bcoef _ _ B ((/ q_fact k) * (/ q_fact k))%Q)).
Proof.
  intros BA bae B a k.
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (@bmult _ _ B (bpow BA bae B a k) (bpow BA bae B (@bopp _ _ B a) k))
             (@bcoef _ _ B ((/ q_fact k) * (/ q_fact k))%Q)) _).
  - exact (binv_bmult_coef_fold _ _ B (bpow BA bae B a k) (bpow BA bae B (@bopp _ _ B a) k)
                                (/ q_fact k) (/ q_fact k)).
  - apply (@bmult_wd _ _ B).
    + exact (@bae_sym _ _ B _ _ (binv_bpow_split _ _ B a k)).
    + apply (@bae_refl _ _ B).
Qed.

(* Even-term seed connection: the square of [: a * (-a)] equals
   [: (a * a) * (a * a)] — with [binv_bpow_opp2] this orients the even
   diagonal terms [: D_{2j}] toward [: a^{4j}]. *)
Lemma binv_bpow_oppmult2 : forall (BA : Set) (bae : BA -> BA -> Set) (B : BanachAlg BA bae) (a : BA),
  bae (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) (Datatypes.S (Datatypes.S 0%nat)))
         (@bmult _ _ B (@bmult _ _ B a a) (@bmult _ _ B a a)).
Proof.
  intros BA bae B a.
  change (bpow BA bae B (@bmult _ _ B a (@bopp _ _ B a)) (Datatypes.S (Datatypes.S 0%nat)))
    with (@bmult _ _ B (@bmult _ _ B (@bone _ _ B) (@bmult _ _ B a (@bopp _ _ B a)))
                   (@bmult _ _ B a (@bopp _ _ B a))).
  apply (@bae_trans _ _ B _
    (@bmult _ _ B (@bmult _ _ B a (@bopp _ _ B a)) (@bmult _ _ B a (@bopp _ _ B a))) _).
  - apply (@bmult_wd _ _ B (@bmult _ _ B (@bone _ _ B) (@bmult _ _ B a (@bopp _ _ B a)))
                       (@bmult _ _ B a (@bopp _ _ B a))
                       (@bmult _ _ B a (@bopp _ _ B a)) (@bmult _ _ B a (@bopp _ _ B a))).
    + exact (@bmult_one_l _ _ B (@bmult _ _ B a (@bopp _ _ B a))).
    + apply (@bae_refl _ _ B).
  - apply (@bae_trans _ _ B _
      (@bmult _ _ B (@bmult _ _ B a a) (@bmult _ _ B (@bopp _ _ B a) (@bopp _ _ B a))) _).
    + (* [(a * (-a)) * (a * (-a))] as [(a * a) * ((-a) * (-a))]: the symmetric
         direction of the four-factor rearrangement. *)
      apply (@bae_sym _ _ B).
      exact (binv_bmult_swap4 _ _ B a (@bopp _ _ B a) a (@bopp _ _ B a)
                (binv_mult_opp_swap _ _ B a)).
    + apply (@bmult_wd _ _ B (@bmult _ _ B a a) (@bmult _ _ B (@bopp _ _ B a) (@bopp _ _ B a))
                         (@bmult _ _ B a a) (@bmult _ _ B a a)).
      * apply (@bae_refl _ _ B).
      * exact (binv_bmult_opp_opp _ _ B a).
Qed.

(* Assembly notes, registered honestly as open at this interface.
   The power face: the vanishing powers of Section 1, their matching
   certificate, and the main anchor (every partial sum of the series of
   [: a + (-a)] equals one).  The product face: the pairing identity of
   Section 2 — once a general binomial theorem retires the paired remainder,
   it merges with the main anchor into the inverse law
   [: e^a * e^{-a} = 1].  The diagonal face: the alternating folding
   [binv_diag_term_pair] with the even-power seeds [binv_bpow_opp2] and
   [binv_bpow_oppmult2] — the sign carrier lives in the power base and the
   rational coefficients stay positive.  The general binomial identity for
   powers of a sum is upstream of this interface and is not attempted
   here. *)
(* Assumption audit of the listed statement. *)
Print Assumptions binv_bpow_opp_add_mesh.
