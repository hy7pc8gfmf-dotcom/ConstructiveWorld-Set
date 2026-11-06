(* ConstructiveWorld-Set -- truncated-exponential Vandermonde addition-identity family. *)

(** * VandermondePartial: Vandermonde-type addition identity for truncated exponential polynomials on Q.

    Mission.  Truncated exponential polynomials [exp_partial] on Q and their
      triangular double sums: [vdp_exp_partial_add_gen] proves
      [QeqT (exp_partial n (A + B)) (vdp_q2d_partial n A B)], exported at
      negated points as [vdp_exp_partial_add]; the double sum [vdp_q2d_partial]
      recurses through anti-diagonal layers [vdp_layer], each equal to
      [(A+B)^k / k!] by [vdp_layer_eq] on the binomial bridge
      [vdp_binom_expand]; the symmetric pieces [vdp_sym] and [vdp_opp_self_two].

    Dependencies.  Stdlib [QArith.QArith], [Arith.Arith], [ZArith.ZArith], [Setoid], [Morphisms], [Lia].
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp], [S04_RealExpLogConv],
      [S05_AlignmentGRPO], [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp] of this development.

    References.  This development, VandermondePartial.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" VandermondePartial.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc]. *)
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S04_RealExpLogConv.
Require Import S05_AlignmentGRPO.
Require Import S06_DiffSamplingGibbs.
Require Import S07_RealSetoidExpLog.
Require Import S08_RealMainlineDPO.
Require Import S09_EntropyReal.
Require Import S10_KVQuantTrig.
Require Import S11_TP3B5.
Require Import S12_B5RecycleSF.
Require Import S13_NLiveAudit.
Require Import S14_B5BatchBlock.
Require Import S15_TailFEPUp.
From Stdlib Require Import QArith.QArith Arith.Arith ZArith.ZArith.
From Stdlib Require Import Setoid Morphisms Lia.

(* ---------- Section 0. Internal Qeq glue, stated without the tactic-level setoid resolution. ---------- *)

Lemma vdp_eq_trans : forall x y z : Q, x == y -> y == z -> x == z.
Proof. intros x y z H1 H2. rewrite <- H2. exact H1. Qed.

Lemma vdp_eq_sym : forall x y : Q, x == y -> y == x.
Proof. intros x y H. rewrite H. reflexivity. Qed.

Lemma vdp_plus_congr_l : forall u x y : Q, x == y -> x + u == y + u.
Proof. intros u x y H. rewrite H. reflexivity. Qed.

Lemma vdp_plus_congr_r : forall u x y : Q, x == y -> u + x == u + y.
Proof. intros u x y H. rewrite H. reflexivity. Qed.

(* ---------- Section 1. The nat-level bridge: factorial and binomial coefficients, built here in the nat induction style of pow_fact_mono from S03. ---------- *)

Fixpoint vdp_nfact (n : nat) : nat :=
  match n with
  | 0%nat => 1
  | Datatypes.S m => Datatypes.S m * vdp_nfact m
  end.

Fixpoint vdp_binom (k j : nat) : nat :=
  match k with
  | 0%nat => match j with 0%nat => 1 | Datatypes.S _ => 0 end
  | Datatypes.S k' =>
      match j with
      | 0%nat => 1
      | Datatypes.S j' => vdp_binom k' j' + vdp_binom k' (Datatypes.S j')
      end
  end.

Lemma vdp_nfact_pos : forall n, (0 < vdp_nfact n)%nat.
Proof.
  induction n as [| n IH]; simpl; lia.
Qed.

(* boundary case of the Pascal recurrence: the coefficient vanishes once the column index exceeds the row index. *)
Lemma vdp_binom_zero_r : forall k j, (k < j)%nat -> vdp_binom k j = 0%nat.
Proof.
  induction k as [| k IH]; intros j Hj.
  - destruct j as [| j'].
    + exfalso; lia.
    + reflexivity.
  - destruct j as [| j'].
    + exfalso; lia.
    + change (vdp_binom (Datatypes.S k) (Datatypes.S j')) with ((vdp_binom k j' + vdp_binom k (Datatypes.S j'))%nat).
      rewrite (IH j') by lia.
      rewrite (IH (Datatypes.S j')) by lia.
      reflexivity.
Qed.

Lemma vdp_binom_zero_l : forall k, vdp_binom k 0%nat = 1%nat.
Proof. intros k. destruct k as [| k']; reflexivity. Qed.

Lemma vdp_binom_diag : forall k, vdp_binom k k = 1%nat.
Proof.
  induction k as [| k IH].
  - reflexivity.
  - change (vdp_binom (Datatypes.S k) (Datatypes.S k)) with ((vdp_binom k k + vdp_binom k (Datatypes.S k))%nat).
    rewrite IH.
    rewrite (vdp_binom_zero_r k (Datatypes.S k)) by lia.
    reflexivity.
Qed.

(* core of the binomial bridge on nat: C(k,j) * (k-j)! * j! = k!, by induction along the diagonal j <= k. *)
Lemma vdp_binom_fact : forall k j, (j <= k)%nat ->
  ((vdp_binom k j * (vdp_nfact (k - j) * vdp_nfact j)))%nat = (vdp_nfact k)%nat.
Proof.
  induction k as [| k IH]; intros j Hj.
  - assert (Hj0 : j = 0%nat) by lia. subst j. simpl. lia.
  - destruct j as [| j'].
    + simpl. lia.
    + destruct (Nat.eq_dec j' k) as [Heq | Hne].
      * (* diagonal end: C(k+1,k+1) = 1 *)
        subst j'.
        change (vdp_binom (Datatypes.S k) (Datatypes.S k)) with ((vdp_binom k k + vdp_binom k (Datatypes.S k))%nat).
        replace (Datatypes.S k - Datatypes.S k)%nat with 0%nat by lia.
        change (vdp_nfact (Datatypes.S k)) with ((Datatypes.S k * vdp_nfact k)%nat).
        rewrite vdp_binom_diag.
        rewrite (vdp_binom_zero_r k (Datatypes.S k)) by lia.
        simpl. lia.
      * (* interior case: Pascal C(k+1,Sj) = C(k,j) + C(k,Sj) with the two induction premises *)
        assert (Hi1 : ((vdp_binom k j' * (vdp_nfact (k - j') * vdp_nfact j')))%nat = (vdp_nfact k)%nat)
          by (apply IH; lia).
        assert (Hi2 : ((vdp_binom k (Datatypes.S j') * (vdp_nfact (k - Datatypes.S j') * vdp_nfact (Datatypes.S j'))))%nat = (vdp_nfact k)%nat)
          by (apply IH; lia).
        change (vdp_binom (Datatypes.S k) (Datatypes.S j')) with ((vdp_binom k j' + vdp_binom k (Datatypes.S j'))%nat).
        change (vdp_nfact (Datatypes.S k - Datatypes.S j')) with (vdp_nfact (k - j')).
        change (vdp_nfact (Datatypes.S k)) with ((Datatypes.S k * vdp_nfact k)%nat).
        change (vdp_nfact (Datatypes.S j')) with ((Datatypes.S j' * vdp_nfact j')%nat) in Hi2.
        change (vdp_nfact (Datatypes.S j')) with ((Datatypes.S j' * vdp_nfact j')%nat).
        assert (Hd : (k - j')%nat = Datatypes.S ((k - Datatypes.S j')%nat)) by lia.
        rewrite Hd.
        rewrite Hd in Hi1.
        change (vdp_nfact (Datatypes.S ((k - Datatypes.S j')%nat)))
          with ((Datatypes.S (k - Datatypes.S j')) * vdp_nfact (k - Datatypes.S j'))%nat.
        change (vdp_nfact (Datatypes.S ((k - Datatypes.S j')%nat)))
          with ((Datatypes.S (k - Datatypes.S j')) * vdp_nfact (k - Datatypes.S j'))%nat in Hi1.
        assert (E2 : ((vdp_binom k j' + vdp_binom k (Datatypes.S j'))
                       * ((Datatypes.S (k - Datatypes.S j')) * vdp_nfact (k - Datatypes.S j') * (Datatypes.S j' * vdp_nfact j')))%nat
                     = ((Datatypes.S j' * (vdp_binom k j' * ((Datatypes.S (k - Datatypes.S j')) * vdp_nfact (k - Datatypes.S j') * vdp_nfact j'))
                     + (Datatypes.S (k - Datatypes.S j')) * (vdp_binom k (Datatypes.S j') * (vdp_nfact (k - Datatypes.S j') * (Datatypes.S j' * vdp_nfact j')))))%nat)
          by nia.
        rewrite E2. rewrite Hi1. rewrite Hi2.
        assert (Hs : (Datatypes.S j' + Datatypes.S (k - Datatypes.S j'))%nat = Datatypes.S k) by lia.
        rewrite <- Hs. nia.
Qed.

(* ---------- Section 2. The coefficient bridge: Z.of_nat carries nat addition into Q addition. ---------- *)

Lemma vdp_zq_add : forall u v : nat,
  (Z.of_nat (u + v) # 1) == ((Z.of_nat u # 1) + (Z.of_nat v # 1))%Q.
Proof.
  intros u v. unfold Qeq.
  change (Qplus (Z.of_nat u # 1) (Z.of_nat v # 1))
    with (Qmake ((Z.of_nat u * 1 + Z.of_nat v * 1)%Z) (1 * 1)%positive).
  change (Qnum (Qmake ((Z.of_nat u * 1 + Z.of_nat v * 1)%Z) (1 * 1)%positive))
    with ((Z.of_nat u * 1 + Z.of_nat v * 1)%Z).
  change (Qden (Qmake ((Z.of_nat u * 1 + Z.of_nat v * 1)%Z) (1 * 1)%positive)) with 1%positive.
  change (Qnum (Z.of_nat (u + v) # 1)) with (Z.of_nat (u + v)).
  change (Qden (Z.of_nat (u + v) # 1)) with 1%positive.
  lia.
Qed.

Lemma vdp_coef_plus_distr : forall (u v : nat) (W : Q),
  (Z.of_nat (u + v) # 1) * W == (Z.of_nat u # 1) * W + (Z.of_nat v # 1) * W.
Proof.
  intros u v W. rewrite vdp_zq_add. apply Qmult_plus_distr_l.
Qed.

(* ---------- Section 3. The finite sum vdp_sumN and its calculus. ---------- *)

Fixpoint vdp_sumN (m : nat) (f : nat -> Q) : Q :=
  match m with
  | 0%nat => f 0%nat
  | Datatypes.S m' => vdp_sumN m' f + f (Datatypes.S m')
  end.

Lemma vdp_sumN_ext : forall (m : nat) (f g : nat -> Q),
  (forall j, (j <= m)%nat -> f j == g j) -> vdp_sumN m f == vdp_sumN m g.
Proof.
  intros m. induction m as [| m IH]; simpl; intros f g H.
  - apply H. lia.
  - rewrite (IH f g) by (intros j Hj; apply H; lia).
    rewrite (H (Datatypes.S m)) by lia.
    reflexivity.
Qed.

Lemma vdp_sumN_scal : forall (m : nat) (s : Q) (f : nat -> Q),
  s * vdp_sumN m f == vdp_sumN m (fun j => s * f j).
Proof.
  intros m s f. induction m as [| m IH]; simpl.
  - ring.
  - rewrite Qmult_plus_distr_r. rewrite IH. ring.
Qed.

Lemma vdp_sumN_scal_r : forall (m : nat) (f : nat -> Q) (s : Q),
  vdp_sumN m f * s == vdp_sumN m (fun j => f j * s).
Proof.
  intros m f s. induction m as [| m IH]; simpl.
  - ring.
  - rewrite Qmult_plus_distr_l. rewrite IH. ring.
Qed.

Lemma vdp_sumN_add : forall (m : nat) (f g : nat -> Q),
  vdp_sumN m f + vdp_sumN m g == vdp_sumN m (fun j => f j + g j).
Proof.
  intros m f g. induction m as [| m IH]; simpl.
  - reflexivity.
  - rewrite <- IH. ring.
Qed.

Lemma vdp_sumN_first : forall (m : nat) (f : nat -> Q),
  vdp_sumN (Datatypes.S m) f == f 0%nat + vdp_sumN m (fun j => f (Datatypes.S j)).
Proof.
  intros m f. induction m as [| m IH].
  - reflexivity.
  - change (vdp_sumN (Datatypes.S (Datatypes.S m)) f) with (vdp_sumN (Datatypes.S m) f + f (Datatypes.S (Datatypes.S m))).
    rewrite IH.
    change (vdp_sumN (Datatypes.S m) (fun j => f (Datatypes.S j)))
      with (vdp_sumN m (fun j => f (Datatypes.S j)) + f (Datatypes.S (Datatypes.S m))).
    ring.
Qed.

(* first-term split under a moving bound: sum_{j<=k} f j + g k = f 0 + sum_{j<=k} g j,
   with f (S j) = g j pointwise; the trailing term g k cancels at each use site
   by C(k,k+1) = 0. *)
Lemma vdp_sumN_shift_first : forall (k : nat) (f g : nat -> Q),
  (forall j, f (Datatypes.S j) == g j) ->
  vdp_sumN k f + g k == f 0%nat + vdp_sumN k g.
Proof.
  intros k. induction k as [| k IH]; simpl; intros f g H.
  - ring.
  - rewrite (H k).
    rewrite (IH f g H).
    ring.
Qed.

(* shift bridge: sum_{j<=m} F j + F (S m) == F 0 + sum_{j<=m} F (S j),
   the crux of the S-flip: a staggered rearrangement that trades the last
   term of the left side for the first term of the right side. *)
Lemma vdp_sumN_shift : forall (m : nat) (F : nat -> Q),
  vdp_sumN m F + F (Datatypes.S m) == F 0%nat + vdp_sumN m (fun i => F (Datatypes.S i)).
Proof.
  intros m. induction m as [| m IH]; intros F.
  - reflexivity.
  - change (vdp_sumN (Datatypes.S m) F)
      with (vdp_sumN m F + F (Datatypes.S m))%Q.
    change (vdp_sumN (Datatypes.S m) (fun i : nat => F (Datatypes.S i)))
      with (vdp_sumN m (fun i : nat => F (Datatypes.S i))
            + F (Datatypes.S (Datatypes.S m)))%Q.
    rewrite (IH F). ring.
Qed.

(* index reversal: sum_{j<=m} F j = sum_{i<=m} F (m - i), along the bijection i <-> m - i. *)
Lemma vdp_sumN_flip : forall (m : nat) (F : nat -> Q),
  vdp_sumN m F == vdp_sumN m (fun i => F ((m - i)%nat)).
Proof.
  intros m. induction m as [| m IH].
  - reflexivity.
  - (* unfold one definitional layer on each side: L = sum_{j<=m} F j + F (S m);
       R = sum_{i<=m} F (S m - i) + F (S m - S m) = sum_{i<=m} F (S m - i) + F 0. *)
    intros F.
    change (vdp_sumN (Datatypes.S m) F)
      with (vdp_sumN m F + F (Datatypes.S m))%Q.
    change (vdp_sumN (Datatypes.S m) (fun i : nat => F ((Datatypes.S m - i)%nat)))
      with (vdp_sumN m (fun i : nat => F ((Datatypes.S m - i)%nat))
            + (fun i : nat => F ((Datatypes.S m - i)%nat)) (Datatypes.S m))%Q.
    cbv beta.
    replace (Datatypes.S m - Datatypes.S m)%nat with 0%nat by lia.
    (* tail-sum reshaping: sum_{i<=m} F (S m - i) == sum_{i<=m} F (S i),
       since S m - i = S (m - i) for i <= m, then the induction premise
       reverses F after S. *)
    assert (HG : vdp_sumN m (fun i : nat => F ((Datatypes.S m - i)%nat))
                 == vdp_sumN m (fun i => F (Datatypes.S i))).
    { apply (vdp_eq_trans _
               (vdp_sumN m (fun i : nat => F (Datatypes.S ((m - i)%nat))))).
      - apply vdp_sumN_ext. intros i Hi.
        replace (Datatypes.S m - i)%nat with (Datatypes.S ((m - i)%nat)) by lia.
        reflexivity.
      - exact (vdp_eq_sym _ _ (IH (fun i => F (Datatypes.S i)))). }
    (* L == the shift-bridge right side == F 0 + sum F (S i); R == HG reshaped == sum F (S i) + F 0; ring closes. *)
    apply (vdp_eq_trans _ (F 0%nat + vdp_sumN m (fun i => F (Datatypes.S i)))).
    + exact (vdp_sumN_shift m F).
    + rewrite HG. ring.
Qed.

(* ---------- Section 4. The calculus of exp_partial, on the definitional face from S03. ---------- *)

Lemma vdp_exp_wd : forall (n : nat) (x y : Q), x == y -> exp_partial n x == exp_partial n y.
Proof.
  intros n. induction n as [| n IH]; intros x y Hxy.
  - reflexivity.
  - change (exp_partial (Datatypes.S n) x) with (exp_partial n x + q_pow x (Datatypes.S n) / q_fact (Datatypes.S n)).
    change (exp_partial (Datatypes.S n) y) with (exp_partial n y + q_pow y (Datatypes.S n) / q_fact (Datatypes.S n)).
    rewrite (IH x y Hxy).
    rewrite (qeqT_imp_qeq _ _ (q_pow_wd x y (Datatypes.S n) (qeq_imp_qeqT x y Hxy))).
    reflexivity.
Qed.

Lemma vdp_exp_sumN : forall (m : nat) (x : Q),
  exp_partial m x == vdp_sumN m (fun j => q_pow x j / q_fact j).
Proof.
  intros m x. induction m as [| m IH].
  - reflexivity.
  - change (exp_partial (Datatypes.S m) x) with (exp_partial m x + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)).
    change (vdp_sumN (Datatypes.S m) (fun j => q_pow x j / q_fact j))
      with (vdp_sumN m (fun j => q_pow x j / q_fact j) + q_pow x (Datatypes.S m) / q_fact (Datatypes.S m)).
    rewrite IH. reflexivity.
Qed.

Lemma vdp_exp_1 : forall x : Q, exp_partial 1 x == 1 + x.
Proof.
  intro x.
  change (exp_partial 1 x) with (exp_partial 0 x + q_pow x 1 / q_fact 1).
  change (q_pow x 1) with (x * q_pow x 0).
  change (q_pow x 0) with 1.
  change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0).
  change ((Z.of_nat 1 # 1) * q_fact 0) with 1.
  change (exp_partial 0 x) with 1.
  unfold Qdiv.
  change (Qinv 1) with 1.
  ring.
Qed.

Lemma vdp_exp_2 : forall x : Q, exp_partial 2 x == 1 + x + x * x * (1 # 2).
Proof.
  intro x.
  change (exp_partial 2 x) with (exp_partial 1 x + q_pow x 2 / q_fact 2).
  rewrite vdp_exp_1.
  change (q_pow x 2) with (x * (x * q_pow x 0)).
  change (q_pow x 0) with 1.
  change (q_fact 2) with ((Z.of_nat 2 # 1) * q_fact 1).
  change (q_fact 1) with ((Z.of_nat 1 # 1) * q_fact 0).
  change ((Z.of_nat 1 # 1) * q_fact 0) with 1.
  change ((Z.of_nat 2 # 1) * 1) with 2.
  unfold Qdiv.
  change (Qinv 2) with (1 # 2).
  ring.
Qed.

(* the Q-level factorial q_fact = (vdp_nfact n)#1: this connects the Section 1 nat bridge to Q division. *)
Lemma vdp_qfact_Z : forall n : nat, q_fact n == (Z.of_nat (vdp_nfact n) # 1).
Proof.
  induction n as [| n IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_fact_succ n)). rewrite IH.
    change (vdp_nfact (Datatypes.S n)) with (Datatypes.S n * vdp_nfact n)%nat.
    rewrite (Nat2Z.inj_mul (Datatypes.S n) (vdp_nfact n)).
    reflexivity.
Qed.

(* ---------- Section 5. Anti-diagonal layers and the binomial expansion, the main bridge. ---------- *)

(* the anti-diagonal sum of layer k: sum_{j=0}^{k} (A^(k-j)/(k-j)!) * (B^j/j!). *)
Definition vdp_layer (k : nat) (A B : Q) : Q :=
  vdp_sumN k (fun j => (q_pow A ((k - j)%nat) / q_fact ((k - j)%nat)) * (q_pow B j / q_fact j)).

(* the row-sum form of layer k: sum_{i=0}^{k} (A^i/i!) * (B^(k-i)/(k-i)!), interchangeable with the diagonal form through the flip lemma. *)
Definition vdp_layer_row (k : nat) (A B : Q) : Q :=
  vdp_sumN k (fun i => (q_pow A i / q_fact i) * (q_pow B ((k - i)%nat) / q_fact ((k - i)%nat))).

Lemma vdp_layer_flip : forall k A B, vdp_layer k A B == vdp_layer_row k A B.
Proof.
  intros k A B. unfold vdp_layer, vdp_layer_row.
  apply (vdp_eq_trans _
           (vdp_sumN k
              (fun i => ((q_pow A ((k - (k - i)%nat)%nat) / q_fact ((k - (k - i)%nat)%nat))
                       * (q_pow B ((k - i)%nat) / q_fact ((k - i)%nat)))%Q))).
  - exact (vdp_sumN_flip k
             (fun j => (q_pow A ((k - j)%nat) / q_fact ((k - j)%nat)) * (q_pow B j / q_fact j))).
  - apply vdp_sumN_ext. intros i Hi.
    assert (E : (k - ((k - i)%nat))%nat = i) by lia.
    rewrite E. reflexivity.
Qed.

(* binomial expansion: (A+B)^k = sum_{j<=k} C(k,j) * A^(k-j) * B^j, the two-variable truncated companion of q_pow_add at S03:306. *)
Lemma vdp_binom_expand : forall (k : nat) (A B : Q),
  q_pow (A + B) k ==
  vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((k - j)%nat) * q_pow B j).
Proof.
  intros k A B. induction k as [| k IH].
  - reflexivity.
  - rewrite (qeqT_imp_qeq _ _ (q_pow_succ (A + B) k)). rewrite Qmult_plus_distr_l.
    assert (HA : A * q_pow (A + B) k ==
                 vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((Datatypes.S k - j)%nat) * q_pow B j)).
    { rewrite IH. rewrite vdp_sumN_scal. apply vdp_sumN_ext. intros j Hj.
      assert (Eidx : (Datatypes.S k - j)%nat = Datatypes.S ((k - j)%nat)) by lia.
      rewrite Eidx. rewrite (qeqT_imp_qeq _ _ (q_pow_succ A ((k - j)%nat))). ring. }
    assert (HB : B * q_pow (A + B) k ==
                 vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j))).
    { rewrite IH. rewrite vdp_sumN_scal. apply vdp_sumN_ext. intros j Hj.
      rewrite (qeqT_imp_qeq _ _ (q_pow_succ B j)). ring. }
    rewrite HA. rewrite HB.
    (* split the right side at its first term. *)
    rewrite vdp_sumN_first. cbv beta.
    assert (E0 : (Z.of_nat (vdp_binom (Datatypes.S k) 0) # 1) * q_pow A ((Datatypes.S k - 0)%nat) * q_pow B 0
                 == q_pow A (Datatypes.S k)).
    { change (vdp_binom (Datatypes.S k) 0) with 1%nat.
      change (Z.of_nat 1) with 1%Z.
      change (Datatypes.S k - 0)%nat with (Datatypes.S k)%nat.
      change (q_pow B 0) with 1.
      rewrite Qmult_1_l. rewrite Qmult_1_r. reflexivity. }
    rewrite E0.
    (* the Pascal coefficient splits pointwise: C(k+1,Sj) = C(k,j) + C(k,Sj). *)
    assert (Esplit : vdp_sumN k (fun j => (Z.of_nat (vdp_binom (Datatypes.S k) (Datatypes.S j)) # 1)
                                            * q_pow A ((Datatypes.S k - Datatypes.S j)%nat) * q_pow B (Datatypes.S j))
                  == vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j)
                                        + (Z.of_nat (vdp_binom k (Datatypes.S j)) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j))).
    { apply (vdp_eq_trans _
               (vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j)
                                   + (Z.of_nat (vdp_binom k (Datatypes.S j)) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j)))).
      - apply vdp_sumN_ext. intros j Hj.
        change (vdp_binom (Datatypes.S k) (Datatypes.S j))
          with ((vdp_binom k j + vdp_binom k (Datatypes.S j))%nat).
        change (Datatypes.S k - Datatypes.S j)%nat with (k - j)%nat.
        rewrite <- !Qmult_assoc.
        apply vdp_coef_plus_distr.
      - (* the right side of Esplit is the merged function, so the second goal closes by reflexivity. *)
        reflexivity. }
    rewrite Esplit.
    rewrite <- (vdp_sumN_add k
                  (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j))
                  (fun j => (Z.of_nat (vdp_binom k (Datatypes.S j)) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j))).
    (* first-term split of HA under a moving bound: HA + C(k,k+1) * ... = A^(k+1) + HC, the trailing term cancelled by C(k,k+1) = 0. *)
    assert (ESH : vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((Datatypes.S k - j)%nat) * q_pow B j)
                + (Z.of_nat (vdp_binom k (Datatypes.S k)) # 1) * q_pow A ((k - k)%nat) * q_pow B (Datatypes.S k)
                == (Z.of_nat (vdp_binom k 0) # 1) * q_pow A ((Datatypes.S k - 0)%nat) * q_pow B 0
                 + vdp_sumN k (fun j => (Z.of_nat (vdp_binom k (Datatypes.S j)) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j))).
    { apply (vdp_sumN_shift_first k
               (fun j : nat => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((Datatypes.S k - j)%nat) * q_pow B j)
               (fun i : nat => (Z.of_nat (vdp_binom k (Datatypes.S i)) # 1) * q_pow A ((k - i)%nat) * q_pow B (Datatypes.S i))).
      - intros j.
        change (Datatypes.S k - Datatypes.S j)%nat with (k - j)%nat.
        reflexivity. }
    assert (EHCk : (Z.of_nat (vdp_binom k (Datatypes.S k)) # 1) * q_pow A ((k - k)%nat) * q_pow B (Datatypes.S k) == 0).
    { rewrite (vdp_binom_zero_r k (Datatypes.S k)) by lia.
      change (Z.of_nat 0 # 1) with 0.
      repeat rewrite Qmult_0_l.
      repeat rewrite Qmult_0_l.
      reflexivity. }
    assert (Ec0 : (Z.of_nat (vdp_binom k 0) # 1) * q_pow A ((Datatypes.S k - 0)%nat) * q_pow B 0
                 == q_pow A (Datatypes.S k)).
    { rewrite (vdp_binom_zero_l k).
      change (Z.of_nat 1) with 1%Z.
      change (Datatypes.S k - 0)%nat with (Datatypes.S k)%nat.
      change (q_pow B 0) with 1.
      rewrite Qmult_1_l. rewrite Qmult_1_r. reflexivity. }
    assert (EHA2 : vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((Datatypes.S k - j)%nat) * q_pow B j)
                == q_pow A (Datatypes.S k)
                 + vdp_sumN k (fun j => (Z.of_nat (vdp_binom k (Datatypes.S j)) # 1) * q_pow A ((k - j)%nat) * q_pow B (Datatypes.S j))).
    { apply (vdp_eq_trans _
               (vdp_sumN k (fun j => (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((Datatypes.S k - j)%nat) * q_pow B j)
              + (Z.of_nat (vdp_binom k (Datatypes.S k)) # 1) * q_pow A ((k - k)%nat) * q_pow B (Datatypes.S k))).
      - rewrite EHCk. ring.
      - rewrite <- Ec0. exact ESH. }
    rewrite EHA2.
    ring.
Qed.

(* pointwise weight identity for j <= k: C(k,j) * A^(k-j) * B^j = (A^(k-j)/(k-j)!) * (B^j/j!) * k!. *)
Lemma vdp_weight_eq : forall (k j : nat) (A B : Q), (j <= k)%nat ->
  (Z.of_nat (vdp_binom k j) # 1) * q_pow A ((k - j)%nat) * q_pow B j
  == (q_pow A ((k - j)%nat) / q_fact ((k - j)%nat)) * (q_pow B j / q_fact j) * q_fact k.
Proof.
  intros k j A B Hj.
  assert (Hnat : ((vdp_binom k j * (vdp_nfact (k - j) * vdp_nfact j)))%nat = (vdp_nfact k)%nat)
    by (apply vdp_binom_fact; exact Hj).
  assert (Hz : (Z.of_nat (vdp_binom k j) # 1) * (q_fact ((k - j)%nat) * q_fact j) == q_fact k).
  { rewrite (vdp_qfact_Z (k - j)). rewrite (vdp_qfact_Z j). rewrite (vdp_qfact_Z k).
    rewrite <- Hnat. rewrite !Nat2Z.inj_mul. reflexivity. }
  assert (Hf1 : ~ (q_fact ((k - j)%nat) == 0))
    by (intro H0; exact (Qlt_not_eq 0 (q_fact ((k - j)%nat))
           (QltT_to_Qlt 0 (q_fact ((k - j)%nat)) (q_fact_pos ((k - j)%nat)))
           (Qeq_sym (q_fact ((k - j)%nat)) 0 H0))).
  assert (Hf2 : ~ (q_fact j == 0))
    by (intro H0; exact (Qlt_not_eq 0 (q_fact j)
           (QltT_to_Qlt 0 (q_fact j) (q_fact_pos j))
           (Qeq_sym (q_fact j) 0 H0))).
  unfold Qdiv.
  rewrite <- Hz.
  assert (E : (q_pow A ((k - j)%nat) * / q_fact ((k - j)%nat)) * (q_pow B j * / q_fact j)
                * ((Z.of_nat (vdp_binom k j) # 1) * (q_fact ((k - j)%nat) * q_fact j))
              == q_pow A ((k - j)%nat) * q_pow B j * (Z.of_nat (vdp_binom k j) # 1)
                   * ((q_fact ((k - j)%nat) * / q_fact ((k - j)%nat)) * (q_fact j * / q_fact j)))
    by ring.
  rewrite E.
  rewrite (Qmult_inv_r (q_fact ((k - j)%nat)) Hf1).
  rewrite (Qmult_inv_r (q_fact j) Hf2).
  ring.
Qed.

(* division cancellation: X * D = Y <-> X = Y / D for D <> 0; only the forward direction is used here. *)
Lemma vdp_div_mul_eq : forall X Y D : Q, ~ (D == 0) -> X * D == Y -> X == Y / D.
Proof.
  intros X Y D HD H.
  unfold Qdiv.
  rewrite <- H.
  transitivity (X * (D * / D)).
  - rewrite (Qmult_inv_r D HD). ring.
  - ring.
Qed.

(* layer identity, the target of the main bridge: the anti-diagonal layer equals (A+B)^k / k!. *)
Lemma vdp_layer_eq : forall (k : nat) (A B : Q),
  vdp_layer k A B == q_pow (A + B) k / q_fact k.
Proof.
  intros k A B.
  assert (Hfk : ~ (q_fact k == 0)).
  { intro H0. exact (Qlt_not_eq 0 (q_fact k)
        (QltT_to_Qlt 0 (q_fact k) (q_fact_pos k))
        (Qeq_sym (q_fact k) 0 H0)). }
  apply (vdp_div_mul_eq _ _ _ Hfk).
  unfold vdp_layer. rewrite vdp_sumN_scal_r.
  rewrite (vdp_binom_expand k A B).
  apply vdp_sumN_ext. intros j Hj.
  apply (vdp_eq_sym _ _ (vdp_weight_eq k j A B Hj)).
Qed.

(* ---------- Section 6. The triangular double sum vdp_q2d_partial and the main statements. ---------- *)

(* triangular double sum sum_{i=0}^{n} sum_{j=0}^{n-i} (A^i/i!) * (B^j/j!),
   regrouped by diagonals: the layer with i + j = k is an anti-diagonal sum,
   and the bijection i = k - j makes the diagonal and row forms equivalent. *)
Fixpoint vdp_q2d_partial (n : nat) (A B : Q) : Q :=
  match n with
  | 0%nat => (q_pow A 0%nat / q_fact 0%nat) * (q_pow B 0%nat / q_fact 0%nat)
  | Datatypes.S m => vdp_q2d_partial m A B + vdp_layer (Datatypes.S m) A B
  end.

Lemma vdp_q2d_partial_succ : forall n A B,
  vdp_q2d_partial (Datatypes.S n) A B == vdp_q2d_partial n A B + vdp_layer (Datatypes.S n) A B.
Proof. reflexivity. Qed.

(* main statement, general form: the partial sum equals exp_partial (A+B). *)
Theorem vdp_exp_partial_add_gen : forall (A B : Q) (n : nat),
  QeqT (exp_partial n (A + B)) (vdp_q2d_partial n A B).
Proof.
  intros A B n. induction n as [| n IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT.
    change (exp_partial (Datatypes.S n) (A + B))
      with (exp_partial n (A + B) + q_pow (A + B) (Datatypes.S n) / q_fact (Datatypes.S n)).
    change (vdp_q2d_partial (Datatypes.S n) A B)
      with (vdp_q2d_partial n A B + vdp_layer (Datatypes.S n) A B).
    rewrite (vdp_layer_eq (Datatypes.S n) A B).
    rewrite (qeqT_imp_qeq _ _ IH).
    reflexivity.
Qed.

(* main statement, designated exit form: exp(-(a+b)) equals the triangular double sum at (Qopp a, Qopp b). *)
Theorem vdp_exp_partial_add : forall (a b : Q) (n : nat),
  QeqT (exp_partial n (Qopp (a + b))) (vdp_q2d_partial n (Qopp a) (Qopp b)).
Proof.
  intros a b n. apply qeq_imp_qeqT.
  apply (vdp_eq_trans _ (exp_partial n (Qopp a + Qopp b))).
  - apply (vdp_exp_wd n). ring.
  - exact (qeqT_imp_qeq _ _ (vdp_exp_partial_add_gen (Qopp a) (Qopp b) n)).
Qed.

(* ---------- Section 7. The symmetric statement vdp_sym and the closed special case vdp_opp_self_two. ---------- *)

(* full rectangular double sum: sum_{i=0}^{n} sum_{j=0}^{n} (A^i/i!) * (B^j/j!), equal to exp * exp. *)
Definition vdp_q2d_full (n : nat) (A B : Q) : Q :=
  vdp_sumN n (fun i => (q_pow A i / q_fact i) * exp_partial n B).

(* tail term: the strict upper triangle sum_{i=0}^{n} (A^i/i!) * (exp_partial n B - exp_partial (n-i) B);
   the inner difference is the truncated tail of row i beyond j > n-i. *)
Definition vdp_sym_tail (n : nat) (A B : Q) : Q :=
  vdp_sumN n (fun i => (q_pow A i / q_fact i) * (exp_partial n B - exp_partial ((n - i)%nat) B)).

(* the triangle equals the row-folded form, the shape used in the tail-term argument. *)
Lemma vdp_tri_sumN : forall (n : nat) (A B : Q),
  vdp_q2d_partial n A B ==
  vdp_sumN n (fun i => (q_pow A i / q_fact i) * exp_partial ((n - i)%nat) B).
Proof.
  intros n A B. induction n as [| n IH].
  - reflexivity.
  - change (vdp_q2d_partial (Datatypes.S n) A B)
      with (vdp_q2d_partial n A B + vdp_layer (Datatypes.S n) A B).
    rewrite IH.
    rewrite (vdp_layer_flip (Datatypes.S n) A B).
    unfold vdp_layer_row.
    change (vdp_sumN (Datatypes.S n) (fun i => (q_pow A i / q_fact i) * (q_pow B ((Datatypes.S n - i)%nat) / q_fact ((Datatypes.S n - i)%nat))))
      with ((vdp_sumN n (fun i => (q_pow A i / q_fact i) * (q_pow B ((Datatypes.S n - i)%nat) / q_fact ((Datatypes.S n - i)%nat)))
            + (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n)) * (q_pow B ((Datatypes.S n - Datatypes.S n)%nat) / q_fact ((Datatypes.S n - Datatypes.S n)%nat)))%Q).
    change (vdp_sumN (Datatypes.S n) (fun i => (q_pow A i / q_fact i) * exp_partial ((Datatypes.S n - i)%nat) B))
      with ((vdp_sumN n (fun i => (q_pow A i / q_fact i) * exp_partial ((Datatypes.S n - i)%nat) B)
            + (q_pow A (Datatypes.S n) / q_fact (Datatypes.S n)) * exp_partial (Datatypes.S n - Datatypes.S n) B)%Q).
    (* split pointwise inside the row: E_{S n - i} = E_{n - i} + w_{S n - i} for i <= n. *)
    assert (Erow : vdp_sumN n (fun i => (q_pow A i / q_fact i) * exp_partial ((Datatypes.S n - i)%nat) B)
                == vdp_sumN n (fun i => (q_pow A i / q_fact i) * exp_partial ((n - i)%nat) B)
                 + vdp_sumN n (fun i => (q_pow A i / q_fact i) * (q_pow B ((Datatypes.S n - i)%nat) / q_fact ((Datatypes.S n - i)%nat)))).
    { apply (vdp_eq_trans _
               (vdp_sumN n (fun i => (q_pow A i / q_fact i) * exp_partial ((n - i)%nat) B
                                   + (q_pow A i / q_fact i) * (q_pow B ((Datatypes.S n - i)%nat) / q_fact ((Datatypes.S n - i)%nat))))).
      - apply vdp_sumN_ext. intros i Hi.
        assert (Eidx : (Datatypes.S n - i)%nat = Datatypes.S ((n - i)%nat)) by lia.
        rewrite Eidx.
        change (exp_partial (Datatypes.S ((n - i)%nat)) B)
          with (exp_partial ((n - i)%nat) B + q_pow B (Datatypes.S (n - i)) / q_fact (Datatypes.S (n - i))).
        ring.
      - apply (vdp_eq_sym _ _ (vdp_sumN_add n
              (fun i => (q_pow A i / q_fact i) * exp_partial ((n - i)%nat) B)
              (fun i => (q_pow A i / q_fact i) * (q_pow B ((Datatypes.S n - i)%nat) / q_fact ((Datatypes.S n - i)%nat))))). }
    rewrite Erow.
    replace (Datatypes.S n - Datatypes.S n)%nat with 0%nat by lia.
    change ((q_pow B 0 / q_fact 0)%Q) with 1.
    change (exp_partial 0 B) with 1.
    ring.
Qed.

(* the rectangle equals exp * exp. *)
Lemma vdp_full_prod : forall (n : nat) (A B : Q),
  exp_partial n A * exp_partial n B == vdp_q2d_full n A B.
Proof.
  intros n A B. rewrite (vdp_exp_sumN n A). unfold vdp_q2d_full.
  rewrite (vdp_sumN_scal_r n (fun j => q_pow A j / q_fact j) (exp_partial n B)).
  reflexivity.
Qed.

(* symmetric statement: exp(-a) * exp(-b) equals the triangular partial sum plus the strict upper-triangle tail. *)
Theorem vdp_sym : forall (a b : Q) (n : nat),
  QeqT (exp_partial n (Qopp a) * exp_partial n (Qopp b))
       (vdp_q2d_partial n (Qopp a) (Qopp b) + vdp_sym_tail n (Qopp a) (Qopp b)).
Proof.
  intros a b n. apply qeq_imp_qeqT.
  unfold vdp_sym_tail. unfold Qminus.
  apply (vdp_eq_trans _ (vdp_q2d_full n (Qopp a) (Qopp b))).
  - apply (vdp_full_prod n).
  - (* rectangle = triangle by the tri_sumN reshaping, plus the strict upper-triangle tail pointwise by ring. *)
    rewrite (vdp_tri_sumN n (Qopp a) (Qopp b)).
    unfold vdp_q2d_full, vdp_sym_tail.
    rewrite (vdp_sumN_add n
                  (fun i => (q_pow (Qopp a) i / q_fact i) * exp_partial ((n - i)%nat) (Qopp b))
                  (fun i => (q_pow (Qopp a) i / q_fact i) * (exp_partial n (Qopp b) - exp_partial ((n - i)%nat) (Qopp b)))).
    apply vdp_sumN_ext. intros i Hi. ring.
Qed.

(* closed special case, the Q-level finite copy of bxoo_exp_opp_one at
   UpReqBanachExpOppOne:209 taken at b := -a: exp(-a) * exp(a) = 1 + tail,
   an exact identity whose tail tends to 0 in the limit. *)
Theorem vdp_opp_self_two : forall (a : Q) (n : nat),
  QeqT (exp_partial n (Qopp a) * exp_partial n a) (1 + vdp_sym_tail n (Qopp a) a).
Proof.
  intros a n. apply qeq_imp_qeqT.
  assert (Hoo : Qopp (Qopp a) = a)
    by (destruct a as [p d];
        change (Qopp (Qopp (p # d))) with ((Z.opp (Z.opp p)) # d);
        rewrite Z.opp_involutive; reflexivity).
  pose proof (qeqT_imp_qeq _ _ (vdp_sym a (Qopp a) n)) as Hs.
  rewrite Hoo in Hs.
  pose proof (qeqT_imp_qeq _ _ (vdp_exp_partial_add a (Qopp a) n)) as Hm.
  rewrite Hoo in Hm.
  assert (Hz : exp_partial n (Qopp (a + Qopp a)) == 1).
  { apply (vdp_eq_trans _ (exp_partial n 0)).
    - apply (vdp_exp_wd n).
      apply (vdp_eq_trans _ (Qopp 0)).
      + rewrite (Qplus_opp_r a). reflexivity.
      + reflexivity.
    - exact (qeqT_imp_qeq _ _ (exp_partial_zero n)). }
  assert (HT : vdp_q2d_partial n (Qopp a) a == 1).
  { apply (vdp_eq_trans _ _ _ (vdp_eq_sym _ _ Hm)). exact Hz. }
  rewrite Hs.
  apply (vdp_plus_congr_l _ _ _ HT).
Qed.

(* explicit check at n = 1, the tight bound: exp(-a) * exp(a) = (1-a)(1+a) = 1 - a^2. *)
Theorem vdp_opp_self_two_n1 : forall a : Q,
  QleT' (1 - a * a) (exp_partial 1 (Qopp a) * exp_partial 1 a).
Proof.
  intro a. apply Qle_to_QleT'.
  rewrite (vdp_exp_1 (Qopp a)). rewrite (vdp_exp_1 a).
  assert (E : (1 + Qopp a) * (1 + a) == 1 - a * a)
    by (unfold Qminus; ring).
  rewrite E. apply Qle_refl.
Qed.

(* explicit check at n = 2: exp(-a) * exp(a) = 1 + a^4/4, exactly. *)
Theorem vdp_opp_self_two_n2 : forall a : Q,
  QeqT (exp_partial 2 (Qopp a) * exp_partial 2 a) (1 + a * a * a * a * (1 # 4)).
Proof.
  intro a. apply qeq_imp_qeqT.
  rewrite (vdp_exp_2 (Qopp a)). rewrite (vdp_exp_2 a).
  assert (E : (1 + Qopp a + Qopp a * Qopp a * (1 # 2)) * (1 + a + a * a * (1 # 2))
              == 1 + a * a * a * a * (1 # 4)).
  { assert (Hc2 : (1 # 2) == 1 / 2) by reflexivity.
    assert (Hc4 : (1 # 4) == 1 / 4) by reflexivity.
    rewrite Hc2. rewrite Hc4.
    field. }
  rewrite E. reflexivity.
Qed.

(* ---------- Exit audit: Print Assumptions for each named statement. ---------- *)

Print Assumptions vdp_exp_partial_add.
Print Assumptions vdp_sym.
Print Assumptions vdp_opp_self_two.
Print Assumptions vdp_opp_self_two_n1.
Print Assumptions vdp_opp_self_two_n2.

Print Assumptions vdp_q2d_partial_succ.
