(* ==========================================================================)
   BeukersLists.v — List form of the Beukers coefficients
   Mission. List-form coefficient machinery for the Beukers irrationality
     proof: the Fixpoint definitions bkC/bk_psd/bkQ/bk_psQ, the Pascal shift
     and binomial identities (bkC_pascal_shift/bk_psd_binom), the integrality
     witness bk_Qn_int (Q_n(1/2) in Z), the lower bound bk_Qn_ge_3pow, the
     evaluation semantics bk_Qn_eval_sem, the harmonic coefficient list bk_H
     and the evaluation bk_Pn_eval of bk_Pn_list.
   Dependencies. S01_BaseRing, S02_CauchyComplete, S03_QExp,
     S07_RealSetoidExpLog (Id/equivalence bridge source); Stdlib QArith,
     Lists.List, Arith, ZArith, Lia.
   References. Coefficient combinatorics of Beukers-type Pade approximation
     (Delannoy numbers and integrality).
   Constructivity. Every piece ends in Qed with zero acknowledged-premise
     word faces and no classical logic; statement faces ride Set-layer
     carriers (order predicates and equality as Set values, zero Prop
     leakage).
   Build. rocq c -native-compiler no -q -Q . "" BeukersLists.v under the
     cpu_guard wrapper (shadow-tree rebuild within one world).
   ========================================================================== *)

From Stdlib Require Import QArith.QArith Lists.List Arith.Arith ZArith.ZArith Lia.
Require Import S01_BaseRing S02_CauchyComplete S03_QExp.
Require Import S07_RealSetoidExpLog.

(* QArith leaks Q_scope (bare numerals would parse as Q constructors); reopen nat first *)
Open Scope nat_scope.

(* ============================================================ *)
(* Section A. nat-level binomial coefficients (Pascal recursion) and symmetry *)
(* ============================================================ *)

(* Pascal-recursive binomial coefficient C(n,k) (the name bkC avoids clashing with the shadowed C) *)
Fixpoint bkC (n k : nat) : nat :=
  match n with
  | 0 => match k with
         | 0 => 1
         | Datatypes.S _ => 0
         end
  | Datatypes.S n' =>
      match k with
      | 0 => 1
      | Datatypes.S k' => bkC n' k' + bkC n' (Datatypes.S k')
      end
  end.

(* Out-of-range piece: C(n,k) = 0 whenever k > n *)
Lemma bkC_out : forall n k : nat, NatLe (Datatypes.S n) k -> Id (bkC n k) 0.
Proof.
  induction n as [| n IH]; intros k Hk; apply RealSetoid.eq_Id.
  - pose proof (NatLe_drop _ _ Hk) as Hk'.
    destruct k as [| k'].
    + lia.
    + reflexivity.
  - pose proof (NatLe_drop _ _ Hk) as Hk'.
    destruct k as [| k'].
    + lia.
    + cbn [bkC].
      assert (Hn1 : n < k') by lia.
      rewrite (RealSetoid.Id_eq _ _ (IH k' (NatLe_lift _ _ Hn1))).
      assert (Hn2 : n < Datatypes.S k') by lia.
      rewrite (RealSetoid.Id_eq _ _ (IH (Datatypes.S k') (NatLe_lift _ _ Hn2))).
      reflexivity.
Qed.

(* Diagonal piece: C(n,n) = 1 *)
Lemma bkC_diag : forall n : nat, Id (bkC n n) 1.
Proof.
  induction n as [| n IH].
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    cbn [bkC].
    rewrite (RealSetoid.Id_eq _ _ IH).
    assert (Hout : Id (bkC n (Datatypes.S n)) 0)
      by (apply bkC_out; apply NatLe_lift; lia).
    rewrite (RealSetoid.Id_eq _ _ Hout).
    reflexivity.
Qed.

(* Positivity piece: C(n,k) >= 1 whenever k <= n *)
Lemma bkC_pos : forall n k : nat, NatLe k n -> NatLe 1 (bkC n k).
Proof.
  induction n as [| n IH]; intros k Hk.
  - pose proof (NatLe_drop _ _ Hk) as Hk'.
    assert (Hk0 : k = 0) by lia. subst k. cbn [bkC]. apply NatLe_lift. lia.
  - destruct k as [| k'].
    + cbn [bkC]. apply NatLe_lift. lia.
    + cbn [bkC].
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : 1 <= bkC n k')
          by (apply NatLe_drop, IH; apply NatLe_lift; lia).
        assert (H2 : 1 <= bkC n (Datatypes.S k'))
          by (apply NatLe_drop, IH; apply NatLe_lift; lia).
        apply NatLe_lift. lia.
      * pose proof (NatLe_drop _ _ Hk) as Hk''.
        assert (Hk'0 : k' = n) by lia. subst k'.
        rewrite (RealSetoid.Id_eq _ _ (bkC_out n (Datatypes.S n) Hk)).
        assert (H1 : 1 <= bkC n n)
          by (apply NatLe_drop, IH; apply NatLe_lift; lia).
        apply NatLe_lift. lia.
Qed.

(* Pointwise Pascal identity: shift(C n)(k) + C(n,k) = C(S n,k) (every k branch definitional) *)
Lemma bkC_pascal_shift : forall n k : nat,
  Id ((match k with
       | 0 => 0
       | Datatypes.S j => bkC n j
       end) + bkC n k) (bkC (Datatypes.S n) k).
Proof.
  intros n k. destruct k as [| j]; apply RealSetoid.eq_Id.
  - destruct n as [| n']; reflexivity.
  - cbn [bkC]. reflexivity.
Qed.

(* Symmetry lemma: C(n,k) = C(n,n-k) (used by the later identities -- P2 interface piece) *)
Lemma bk_Qn_sym : forall n k : nat, NatLe k n -> Id (bkC n k) (bkC n (n - k)).
Proof.
  induction n as [| n IH]; intros k Hk.
  - pose proof (NatLe_drop _ _ Hk) as Hk'.
    assert (Hk0 : k = 0) by lia. subst k.
    apply RealSetoid.eq_Id. reflexivity.
  - pose proof (NatLe_drop _ _ Hk) as Hk'.
    destruct k as [| k']; apply RealSetoid.eq_Id.
    + replace (Datatypes.S n - 0) with (Datatypes.S n) by lia.
      rewrite (RealSetoid.Id_eq _ _ (bkC_diag (Datatypes.S n))). reflexivity.
    + replace (Datatypes.S n - Datatypes.S k') with (n - k') by lia.
      destruct (le_lt_dec (Datatypes.S k') n) as [Hle | Hlt].
      * assert (H1 : Id (bkC n k') (bkC n (n - k')))
          by (apply IH; apply NatLe_lift; lia).
        assert (H2 : Id (bkC n (Datatypes.S k')) (bkC n (n - Datatypes.S k')))
          by (apply IH; apply NatLe_lift; lia).
        assert (Hn1 : n - k' = Datatypes.S (n - Datatypes.S k')) by lia.
        rewrite Hn1 in H1.
        rewrite Hn1.
        cbn [bkC].
        rewrite (RealSetoid.Id_eq _ _ H1).
        rewrite (RealSetoid.Id_eq _ _ H2).
        lia.
      * assert (Hk'0 : k' = n) by lia. subst k'.
        replace (n - n) with 0 by lia.
        rewrite (RealSetoid.Id_eq _ _ (bkC_diag (Datatypes.S n))).
        reflexivity.
Qed.

(* ============================================================ *)
(* Section B. nat-level falling-power weighted sum bk_psd and the binomial theorem for (1+2)^n *)
(*   bk_psd f n = sum_{k<n} f(k) * 2^{n-1-k}; the recursion is                  *)
(*   bk_psd f (S m) = 2 * bk_psd f m + f m (the falling-power step is exactly doubling). *)
(* ============================================================ *)

Fixpoint bk_psd (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | Datatypes.S m => 2 * bk_psd f m + f m
  end.

Lemma bk_psd_ext : forall (N : nat) (f g : nat -> nat),
  (forall k : nat, NatLe (Datatypes.S k) N -> Id (f k) (g k)) ->
  Id (bk_psd f N) (bk_psd g N).
Proof.
  induction N as [| N IH]; intros f g H.
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    cbn [bk_psd].
    assert (HP : forall k : nat, NatLe (Datatypes.S k) N -> Id (f k) (g k))
      by (intro k; intro Hk; pose proof (NatLe_drop _ _ Hk);
          apply H; apply NatLe_lift; lia).
    rewrite (RealSetoid.Id_eq _ _ (IH f g HP)).
    rewrite (RealSetoid.Id_eq _ _
               (H N (NatLe_lift _ _ (le_n (Datatypes.S N))))).
    reflexivity.
Qed.

Lemma bk_psd_add : forall (N : nat) (f g : nat -> nat),
  Id (bk_psd (fun k => f k + g k) N) (bk_psd f N + bk_psd g N).
Proof.
  induction N as [| N IH]; intros f g.
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    cbn [bk_psd]. rewrite (RealSetoid.Id_eq _ _ (IH f g)). lia.
Qed.

(* Shift piece: shifting the whole coefficient row right by one (zero head) gives a sum one level lower *)
Lemma bk_psd_shift : forall (m : nat) (g : nat -> nat),
  Id (bk_psd (fun k => match k with
                       | 0 => 0
                       | Datatypes.S j => g j
                       end) (Datatypes.S m)) (bk_psd g m).
Proof.
  induction m as [| m IH]; intros g.
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    assert (Hunf : bk_psd (fun k => match k with
                                    | 0 => 0
                                    | Datatypes.S j => g j
                                    end) (Datatypes.S (Datatypes.S m))
                 = 2 * bk_psd (fun k => match k with
                                        | 0 => 0
                                        | Datatypes.S j => g j
                                        end) (Datatypes.S m)
                   + g m)
      by reflexivity.
    rewrite Hunf, (RealSetoid.Id_eq _ _ (IH g)). reflexivity.
Qed.

(* Falling-power binomial theorem: sum_{k<=n} C(n,k) * 2^{n-k} = (1+2)^n = 3^n
   (stdlib has no binomial theorem; self-built -- see the header for the survey) *)
Lemma bk_psd_binom : forall n : nat,
  Id (bk_psd (fun k => bkC n k) (Datatypes.S n)) (3 ^ n).
Proof.
  induction n as [| n IH].
  - apply RealSetoid.eq_Id.
    cbn [bk_psd]. replace (2 * 0)%nat with 0%nat by lia. reflexivity.
  - apply RealSetoid.eq_Id.
    replace (bk_psd (fun k => bkC (Datatypes.S n) k) (Datatypes.S (Datatypes.S n)))
      with (bk_psd (fun k => (match k with
                             | 0 => 0
                             | Datatypes.S j => bkC n j
                             end) + bkC n k) (Datatypes.S (Datatypes.S n)))
      by (apply RealSetoid.Id_eq; apply bk_psd_ext; intro k; intro Hk;
          apply bkC_pascal_shift).
    assert (Hadd : bk_psd (fun k => (match k with
                                    | 0 => 0
                                    | Datatypes.S j => bkC n j
                                    end) + bkC n k) (Datatypes.S (Datatypes.S n))
                 = bk_psd (fun k => match k with
                                    | 0 => 0
                                    | Datatypes.S j => bkC n j
                                    end) (Datatypes.S (Datatypes.S n))
                   + bk_psd (bkC n) (Datatypes.S (Datatypes.S n)))
      by (apply RealSetoid.Id_eq; apply bk_psd_add).
    rewrite Hadd.
    assert (IH' : Id (bk_psd (bkC n) (Datatypes.S n)) (3 ^ n)) by exact IH.
    assert (Hsh : bk_psd (fun k => match k with
                                   | 0 => 0
                                   | Datatypes.S j => bkC n j
                                   end) (Datatypes.S (Datatypes.S n))
                = bk_psd (bkC n) (Datatypes.S n))
      by (apply RealSetoid.Id_eq; apply (bk_psd_shift (Datatypes.S n) (bkC n))).
    assert (Hunf : bk_psd (bkC n) (Datatypes.S (Datatypes.S n))
                 = 2 * bk_psd (bkC n) (Datatypes.S n)
                   + bkC n (Datatypes.S n))
      by reflexivity.
    rewrite Hsh, Hunf, (RealSetoid.Id_eq _ _ IH').
    rewrite (RealSetoid.Id_eq _ _
               (bkC_out n (Datatypes.S n)
                  (NatLe_lift _ _ (Nat.lt_succ_diag_r n)))).
    rewrite Nat.pow_succ_r'.
    lia.
Qed.

(* Monotone piece: pointwise order implies order of the sums *)
Lemma bk_psd_mono : forall (N : nat) (f h : nat -> nat),
  (forall k : nat, NatLe (Datatypes.S k) N -> NatLe (f k) (h k)) ->
  NatLe (bk_psd f N) (bk_psd h N).
Proof.
  induction N as [| N IH]; intros f h H.
  - apply NatLe_lift. reflexivity.
  - cbn [bk_psd].
    assert (H1 : bk_psd f N <= bk_psd h N)
      by (apply NatLe_drop, IH; intro k; intro Hk;
          exact (H k (NatLe_lift _ _
                        (le_S _ _ (NatLe_drop _ _ Hk))))).
    assert (H2 : f N <= h N)
      by (apply NatLe_drop, H; apply NatLe_lift; lia).
    apply NatLe_lift. lia.
Qed.

(* ============================================================ *)
(* Section C. nat-level q~_n and the 3^n lower bound (nat scaffolding face) *)
(* ============================================================ *)

(* q~_n := sum_{k<=n} C(n,k)^2 * 2^{n-k} (the nat carrier of 2^n * Q_n(1/2)) *)
Definition bk_Qn_qtilde (n : nat) : nat :=
  bk_psd (fun k => bkC n k * bkC n k) (Datatypes.S n).

Lemma bk_Qn_ge_3pow_nat : forall n : nat, NatLe (3 ^ n) (bk_Qn_qtilde n).
Proof.
  intro n.
  unfold bk_Qn_qtilde.
  assert (Hpt : forall k : nat,
            NatLe (Datatypes.S k) (Datatypes.S n) ->
            NatLe (bkC n k) (bkC n k * bkC n k)).
  { intro k. intro Hk.
    pose proof (NatLe_drop _ _ Hk) as HkD.
    assert (Hk' : k <= n) by lia.
    assert (Hpos := bkC_pos n k (NatLe_lift _ _ Hk')).
    apply NatLe_drop in Hpos.
    apply NatLe_lift. nia. }
  assert (Hmono := bk_psd_mono (Datatypes.S n)
                     (fun k => bkC n k)
                     (fun k => bkC n k * bkC n k) Hpt).
  rewrite <- (RealSetoid.Id_eq _ _ (bk_psd_binom n)).
  exact Hmono.
Qed.

(* nat-to-Q bridge: the Q image of the nat order *)
Lemma bk_Qle_nat : forall a b : nat, NatLe a b -> QleT' (Z.of_nat a # 1) (Z.of_nat b # 1).
Proof.
  intros a b H.
  apply Qle_to_QleT'. unfold Qle. cbn [Qnum Qden].
  rewrite !Z.mul_1_r.
  apply Nat2Z.inj_le.
  apply NatLe_drop. exact H.
Qed.

(* ============================================================ *)
(* Section D. Q layer: the Q_n coefficient list, evaluation semantics and the integrality witness *)
(* ============================================================ *)

(* Horner fold evaluation (head is the constant term) *)
Fixpoint bkQ (p : list Q) (z : Q) : Q :=
  match p with
  | nil => 0%Q
  | c :: p' => c + z * bkQ p' z
  end.

(* Index list core: bk_idx N = [0;1;...;N-1] (letters carried by a list Fixpoint) *)
Fixpoint bk_idx (N : nat) : list nat :=
  match N with
  | 0 => nil
  | Datatypes.S m => bk_idx m ++ (m :: nil)
  end.

Lemma bk_idx_seq : forall N : nat, Id (bk_idx N) (seq 0 N).
Proof.
  induction N as [| N IH].
  - apply RealSetoid.eq_Id. reflexivity.
  - apply RealSetoid.eq_Id.
    cbn [bk_idx]. rewrite (RealSetoid.Id_eq _ _ IH).
    rewrite (seq_S N 0). reflexivity.
Qed.

(* Q_n coefficient list: term k is C(n,k)^2 (the Q image of bkC squared), k = 0..n *)
Definition bk_Qn_list (n : nat) : list Q :=
  map (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (bk_idx (Datatypes.S n)).

(* Evaluation function (list-fold face) *)
Definition bk_Qn_eval (n : nat) (z : Q) : Q := bkQ (bk_Qn_list n) z.

(* Q-layer indexed sum core: bk_psQ f N z = sum_{k<N} f(k) * z^k *)
Fixpoint bk_psQ (f : nat -> Q) (N : nat) (z : Q) : Q :=
  match N with
  | 0 => 0%Q
  | Datatypes.S m => bk_psQ f m z + f m * q_pow z m
  end.

Lemma bkQ_app : forall (p q : list Q) (z : Q),
  QeqT (bkQ (p ++ q) z) (bkQ p z + q_pow z (length p) * bkQ q z)%Q.
Proof.
  induction p as [| a p' IH]; intros q z.
  - apply qeq_imp_qeqT. cbn [app length bkQ q_pow]. ring.
  - apply qeq_imp_qeqT.
    cbn [app length bkQ].
    rewrite (qeqT_imp_qeq _ _ (IH q z)).
    rewrite (qeqT_imp_qeq _ _ (q_pow_succ z (length p'))).
    ring.
Qed.

(* List vs indexed sum: bkQ (map f (seq 0 (S N))) z == sum_{k<S N} f(k) * z^k *)
Lemma bkQ_seq_map : forall (N : nat) (f : nat -> Q) (z : Q),
  QeqT (bkQ (map f (seq 0 (Datatypes.S N))) z) (bk_psQ f (Datatypes.S N) z).
Proof.
  induction N as [| N IH]; intros f z.
  - apply qeq_imp_qeqT. cbn [seq map bkQ bk_psQ q_pow]. ring.
  - apply qeq_imp_qeqT.
    replace (seq 0 (Datatypes.S (Datatypes.S N)))
      with (seq 0 (Datatypes.S N) ++ (Datatypes.S N :: nil))
      by (rewrite (seq_S (Datatypes.S N) 0); reflexivity).
    rewrite map_app.
    rewrite (qeqT_imp_qeq _ _ (bkQ_app (map f (seq 0 (Datatypes.S N)))
                                        (f (Datatypes.S N) :: nil) z)).
    rewrite map_length, seq_length.
    cbn [map bkQ].
    rewrite (qeqT_imp_qeq _ _ (IH f z)).
    assert (Hunf : bk_psQ f (Datatypes.S (Datatypes.S N)) z
                 = (bk_psQ f (Datatypes.S N) z
                    + f (Datatypes.S N) * q_pow z (Datatypes.S N))%Q)
      by reflexivity.
    rewrite Hunf.
    ring.
Qed.

(* Termwise image: the k-th term of map+seq equals f k once k is in range *)
Lemma bk_nth_map_lt : forall (f : nat -> Q) (l : list nat) (k : nat) (d : Q),
  NatLe (Datatypes.S k) (length l) ->
  QeqT (nth k (map f l) d) (f (nth k l 0)).
Proof.
  intros f l. induction l as [| a l' IH]; intros k d Hk.
  - exfalso. apply NatLe_drop in Hk. cbn [length] in Hk. lia.
  - destruct k as [| k'].
    + apply qeq_imp_qeqT. cbn [map nth]. apply Qeq_refl.
    + cbn [map nth]. apply IH. cbn [length] in Hk.
      pose proof (NatLe_drop _ _ Hk). apply NatLe_lift. lia.
Qed.

Lemma bk_nth_map_seq : forall (f : nat -> Q) (N k : nat) (d : Q),
  NatLe (Datatypes.S k) (Datatypes.S N) ->
  QeqT (nth k (map f (seq 0 (Datatypes.S N))) d) (f k).
Proof.
  intros f N k d Hk.
  replace (f k) with (f (nth k (seq 0 (Datatypes.S N)) 0)).
  - apply (bk_nth_map_lt f (seq 0 (Datatypes.S N)) k d).
    rewrite seq_length. exact Hk.
  - apply f_equal. rewrite seq_nth by (apply NatLe_drop; exact Hk). reflexivity.
Qed.

(* Termwise description of the coefficients: term k is the Q image of C(n,k)^2 *)
Lemma bk_Qn_list_nth : forall n k : nat,
  NatLe (Datatypes.S k) (Datatypes.S n) ->
  QeqT (nth k (bk_Qn_list n) 0%Q) ((Z.of_nat (bkC n k * bkC n k) # 1)%Q).
Proof.
  intros n k Hk.
  unfold bk_Qn_list. rewrite (RealSetoid.Id_eq _ _ (bk_idx_seq (Datatypes.S n))).
  apply bk_nth_map_seq. exact Hk.
Qed.

(* ============================================================ *)
(* Section D2. The base-change core and the integrality witness (the nontrivial main pieces) *)
(* ============================================================ *)

Lemma bk_q_pow_mul : forall (x y : Q) (k : nat),
  QeqT (q_pow (x * y) k) (q_pow x k * q_pow y k)%Q.
Proof.
  intros x y k. induction k as [| k IH].
  - apply qeq_imp_qeqT. cbn [q_pow]. ring.
  - apply qeq_imp_qeqT. cbn [q_pow]. rewrite (qeqT_imp_qeq _ _ IH). ring.
Qed.

Lemma bk_q_pow_one : forall k : nat, QeqT (q_pow 1%Q k) 1%Q.
Proof.
  induction k as [| k IH].
  - apply qeq_imp_qeqT. reflexivity.
  - apply qeq_imp_qeqT. cbn [q_pow]. rewrite (qeqT_imp_qeq _ _ IH). reflexivity.
Qed.

Lemma bk_Qmul_nat : forall a b : nat,
  QeqT ((Z.of_nat a # 1) * (Z.of_nat b # 1)%Q) (Z.of_nat (a * b) # 1)%Q.
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qmult Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_mul. reflexivity.
Qed.

Lemma bk_Qadd_nat : forall a b : nat,
  QeqT ((Z.of_nat a # 1) + (Z.of_nat b # 1)%Q) (Z.of_nat (a + b) # 1)%Q.
Proof.
  intros a b. apply qeq_imp_qeqT. unfold Qeq. cbn [Qnum Qden Qplus Pos.mul].
  rewrite !Z.mul_1_r, !Nat2Z.inj_add. reflexivity.
Qed.

(* Base-change core (the nontrivial main piece): 2^n * sum_{k<S n} Q#f(k) * (1/2)^k == Q#sum_{k<S n} f(k) 2^{n-k}
   -- carried by the falling-power nat sum bk_psd; pure pointwise induction, no symmetric rearrangement *)
Lemma bk_half_psd : forall (n : nat) (g : nat -> nat),
  QeqT (q_pow (2 # 1)%Q n
    * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q) (Datatypes.S n) (1 # 2)%Q)%Q
       ((Z.of_nat (bk_psd g (Datatypes.S n)) # 1)%Q).
Proof.
  intros n g. induction n as [| n IH].
  - apply qeq_imp_qeqT.
    cbn [q_pow bk_psQ bk_psd].
    replace (2 * 0)%nat with 0%nat by lia.
    cbn [Nat.add]. ring.
  - apply qeq_imp_qeqT.
    assert (Hhalf : (2 # 1)%Q * (1 # 2)%Q == 1%Q)
      by (compute; reflexivity).
    assert (Hunf : bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S (Datatypes.S n)) (1 # 2)%Q
                 = (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                     (Datatypes.S n) (1 # 2)%Q
                   + ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))%Q)%Q)
      by reflexivity.
    rewrite Hunf.
    rewrite Qmult_plus_distr_r.
    assert (EA : q_pow (2 # 1)%Q (Datatypes.S n)
                   * bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                       (Datatypes.S n) (1 # 2)%Q
                 == (Z.of_nat (2 * bk_psd g (Datatypes.S n)) # 1)%Q).
    { rewrite (qeqT_imp_qeq _ _ (q_pow_succ (2 # 1)%Q n)).
      rewrite <- (Qmult_assoc (2 # 1)%Q (q_pow (2 # 1)%Q n)
                    (bk_psQ (fun k => (Z.of_nat (g k) # 1)%Q)
                        (Datatypes.S n) (1 # 2)%Q)).
      rewrite (qeqT_imp_qeq _ _ IH).
      replace (2 # 1)%Q with (Z.of_nat 2 # 1)%Q by reflexivity.
      apply qeqT_imp_qeq. apply bk_Qmul_nat. }
    assert (EB : q_pow (2 # 1)%Q (Datatypes.S n)
                   * ((Z.of_nat (g (Datatypes.S n)) # 1)
                        * q_pow (1 # 2)%Q (Datatypes.S n))
                 == (Z.of_nat (g (Datatypes.S n)) # 1) * 1%Q).
    { transitivity ((Z.of_nat (g (Datatypes.S n)) # 1)
                      * (q_pow (2 # 1)%Q (Datatypes.S n)
                           * q_pow (1 # 2)%Q (Datatypes.S n)))%Q.
      - ring.
      - rewrite <- (qeqT_imp_qeq _ _
                      (bk_q_pow_mul (2 # 1)%Q (1 # 2)%Q (Datatypes.S n))).
        rewrite Hhalf.
        rewrite (qeqT_imp_qeq _ _ (bk_q_pow_one (Datatypes.S n))).
        reflexivity. }
    rewrite EA, EB, Qmult_1_r.
    apply qeqT_imp_qeq. apply bk_Qadd_nat.
Qed.

(* Half-integer closed form: the 2^n lifting of bkQ (bk_Qn_list n) (1/2) equals Q#q~_n *)
Lemma bk_Qn_half_closed : forall n : nat,
  QeqT (q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q
       ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  apply qeq_imp_qeqT.
  unfold bk_Qn_list.
  rewrite (RealSetoid.Id_eq _ _ (bk_idx_seq (Datatypes.S n))).
  rewrite (qeqT_imp_qeq _ _ (bkQ_seq_map n
               (fun k : nat => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (1 # 2)%Q)).
  apply qeqT_imp_qeq. apply bk_half_psd.
Qed.

(* Main piece 2: the integrality witness q~_n = 2^n * Q_n(1/2) in Z (sigT + QeqT, Set face) *)
Theorem bk_Qn_int : forall n : nat,
  sigT (fun z : Z =>
    QeqT ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q) ((z # 1)%Q)).
Proof.
  intro n.
  exact (@existT _ (fun z : Z =>
    QeqT ((q_pow (2 # 1)%Q n * bkQ (bk_Qn_list n) (1 # 2)%Q)%Q) ((z # 1)%Q))
    (Z.of_nat (bk_Qn_qtilde n))
    (bk_Qn_half_closed n)).
Qed.

(* Main piece 3: q~_n >= 3^n (QleT' Set face) *)
Theorem bk_Qn_ge_3pow : forall n : nat,
  QleT' ((Z.of_nat (3 ^ n) # 1)%Q) ((Z.of_nat (bk_Qn_qtilde n) # 1)%Q).
Proof.
  intro n.
  exact (bk_Qle_nat (3 ^ n) (bk_Qn_qtilde n) (bk_Qn_ge_3pow_nat n)).
Qed.

(* Evaluation semantics: bk_Qn_eval n z == sum_{k<=n} C(n,k)^2 * z^k (QeqT Set face) *)
Theorem bk_Qn_eval_sem : forall (n : nat) (z : Q),
  QeqT (bk_Qn_eval n z)
       (bk_psQ (fun k => (Z.of_nat (bkC n k * bkC n k) # 1)%Q) (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Qn_eval, bk_Qn_list.
  rewrite (RealSetoid.Id_eq _ _ (bk_idx_seq (Datatypes.S n))).
  apply bkQ_seq_map.
Qed.

(* ============================================================ *)
(* Section E. The P_n harmonic coefficient list (Q-layer carrier; integrality left to a later closing piece) *)
(* ============================================================ *)

(* Harmonic numbers H_k = sum_{j=1}^{k} 1/j (Q-layer Fixpoint) *)
Fixpoint bk_H (k : nat) : Q :=
  match k with
  | 0 => 0%Q
  | Datatypes.S k' => bk_H k' + (1%Q / (Z.of_nat (Datatypes.S k') # 1))%Q
  end.

(* P_n coefficient list: term k is C(n,k)^2 * H_k *)
Definition bk_Pn_list (n : nat) : list Q :=
  map (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
      (bk_idx (Datatypes.S n)).

(* Evaluation semantics: bkQ (bk_Pn_list n) z == sum_{k<=n} C(n,k)^2 * H_k * z^k (QeqT Set face) *)
Theorem bk_Pn_eval : forall (n : nat) (z : Q),
  QeqT (bkQ (bk_Pn_list n) z)
       (bk_psQ (fun k => ((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q)
               (Datatypes.S n) z).
Proof.
  intros n z. unfold bk_Pn_list.
  rewrite (RealSetoid.Id_eq _ _ (bk_idx_seq (Datatypes.S n))).
  apply bkQ_seq_map.
Qed.

(* Termwise description of the P_n coefficients *)
Lemma bk_Pn_list_nth : forall n k : nat,
  NatLe (Datatypes.S k) (Datatypes.S n) ->
  QeqT (nth k (bk_Pn_list n) 0%Q)
       (((Z.of_nat (bkC n k * bkC n k) # 1) * bk_H k)%Q).
Proof.
  intros n k Hk.
  unfold bk_Pn_list. rewrite (RealSetoid.Id_eq _ _ (bk_idx_seq (Datatypes.S n))).
  apply bk_nth_map_seq. exact Hk.
Qed.

(* ============================================================ *)
(* Assumption audit trail: Print Assumptions (final review anchor) *)
(* ============================================================ *)

Print Assumptions bk_Qn_sym.
Print Assumptions bk_psd_binom.
Print Assumptions bk_Qn_ge_3pow_nat.
Print Assumptions bk_Qn_int.
Print Assumptions bk_Qn_ge_3pow.
Print Assumptions bk_Qn_eval_sem.
Print Assumptions bk_Qn_list_nth.
Print Assumptions bk_Pn_eval.
Print Assumptions bk_Pn_list_nth.
