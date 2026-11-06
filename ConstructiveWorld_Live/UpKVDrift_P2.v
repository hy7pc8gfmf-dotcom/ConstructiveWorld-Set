(* ConstructiveWorld-Set -- kernel-drift family: kept/dropped kernel rows, explicit premise giving, TV drift bounds. *)

(** * UpKVDrift_P2: row-TV identities and two-kernel drift bounds.

    Mission.  Formalizes the second segment of the kernel-drift chain on a
      finite state world whose kernel rows split into kept and dropped
      parts: positivity of the kept mass [Z_keep_pos] and of the row count
      [N_R_pos], the exact row-total-variation identity [kev_row_tv_exact]
      with corollaries [kev_row_tv_bound] and [kev_row_tv_one_minus_Z], and
      the two-kernel drift bound [kv_drift_bound] and [kv_drift_bound_tv].

    Dependencies.  [Datatypes]/[List] via the prelude; no Stdlib Require in
      this file (extraction verification is gate7's Separate Extraction driver).
      Requires [S01_BaseRing], [S02_CauchyComplete], [S03_QExp],
      [S04_RealExpLogConv], [S05_AlignmentGRPO], [S06_DiffSamplingGibbs],
      [S07_RealSetoidExpLog], [S08_RealMainlineDPO], [S09_EntropyReal],
      [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF], [S13_NLiveAudit],
      [S14_B5BatchBlock], [S15_TailFEPUp] of this development.

    References.  This development, UpKVDrift_P2.v, the baseline module in
      ConstructiveWorld-Main whose statement names are carried over here
      verbatim (statement-face Set-carrier completion).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); statements
      extract with [Obj.magic] = 0 and no erasure; [coqchk] reports
      [Axioms: none].

    Build.  [coqc -native-compiler no -q -Q . "" UpKVDrift_P2.v] compiles cleanly
      (exit 0); the artifact starts with [436f7121 000160bc] (9.3-era magic). *)
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

Section UpKVDrift.

(* ---------- 0. The contract world (carried over verbatim from the
   baseline contract; keep_nonempty resolves to
   InT s states + Id (keep s) true, in Set-level form) ---------- *)

Variable Tok : Set.
Variable states : list Tok.
Variable states_ne : Not (Id states (@nil Tok)).
Variable K : Tok -> Tok -> Real.
Variable Krow : forall s : Tok,
  real_eq (real_list_sum Tok (fun s' : Tok => K s s') states) real_one.
Variable Kpos : forall s s' : Tok, real_lt real_zero (K s s').
Variable keep : Tok -> bool.
Variable keep_nonempty :
  sigT (fun s : Tok => And (Id (keep s) true) (InT s states)).

(* Id transports proofs along the type shape (for the bool projection;
   this sidesteps the Prop-level std equality) *)
Lemma kv_id_transport : forall (A : Set) (x y : A) (P : A -> Set),
  P x -> Id x y -> P y.
Proof.
  intros A x y P p H. exact (match H with id_refl => p end).
Qed.

Definition Z_keep (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then K s s' else real_zero) states.

(* Positivity of the size of a nonempty finite list (direct use of
   states_ne; feeds the kv_ofnat family) *)
Lemma kv_ofnat_nonneg : forall k : nat, real_le real_zero (real_of_nat k).
Proof.
  intro k. induction k as [| k IH].
  - apply real_le_refl.
  - cbn [real_of_nat].
    apply (RealSetoid.real_le_id_l real_zero
             (real_plus real_zero real_zero)
             (real_plus real_one (real_of_nat k))).
    + apply real_eq_sym. apply real_plus_zero.
    + apply real_le_plus_compat.
      * apply real_le_from_lt_aux. apply real_lt_zero_one.
      * exact IH.
Qed.

Lemma kv_ofnat_S_pos : forall k : nat,
  real_lt real_zero (real_of_nat (Datatypes.S k)).
Proof.
  intro k. cbn [real_of_nat].
  apply (real_lt_le_trans real_zero real_one
           (real_plus real_one (real_of_nat k)) real_lt_zero_one).
  apply real_le_plus_nonneg_r_aux.
  apply kv_ofnat_nonneg.
Qed.

Lemma kv_N_pos : real_lt real_zero (real_of_nat (length states)).
Proof.
  revert states_ne.
  induction states as [| x rest IH]; intro Hne.
  - exact (match Hne (@id_refl _ (@nil Tok)) with end).
  - cbn [length].
    exact (kv_ofnat_S_pos (length rest)).
Qed.

(* A single term is at most the whole sum (induction on the InT       *)
(* derivation itself; the nil contradiction branch stays outside the  *)
(* extraction closure, so extraction keeps Obj.magic = 0; the in-root *)
(* single_le_sum_aux carries an empty match that would extract two    *)
(* Obj.magic nodes, hence the local reconstruction).                  *)
Lemma kv_single_le_sum : forall (A : Set) (f : A -> Real) (x : A) (l : list A),
  InT x l -> (forall y : A, real_le real_zero (f y)) ->
  real_le (f x) (real_list_sum A f l).
Proof.
  intros A f x l Hin. induction Hin as [l0 | y l0 Hin IH].
  - intro Hnn. cbn [real_list_sum].
    apply real_le_plus_nonneg_r_aux.
    apply (real_list_sum_nonneg A f l0 Hnn).
  - intro Hnn. cbn [real_list_sum].
    apply (real_le_trans _ (real_list_sum A f l0)).
    + exact (IH Hnn).
    + apply (RealSetoid.real_le_id_r (real_list_sum A f l0)
               (real_plus (real_list_sum A f l0) (f y))
               (real_plus (f y) (real_list_sum A f l0))
               (real_plus_comm (real_list_sum A f l0) (f y))).
      apply real_le_plus_nonneg_r_aux. apply Hnn.
Qed.

(* Positivity of Z_keep, stated as a theorem (as in UpKVEv.v: the kept
   witness entry K(s,s0) > 0 and <= Z_keep s; the baseline contract's
   Z_keep_pos premise is thereby discharged) *)
Theorem Z_keep_pos : forall s : Tok, real_lt real_zero (Z_keep s).
Proof.
  intro s.
  destruct keep_nonempty as [s0 [Hk0 Hin0]].
  assert (Hlt0 : real_lt real_zero (if keep s0 then K s s0 else real_zero)).
  { apply (kv_id_transport bool true (keep s0)
             (fun b : bool => real_lt real_zero (if b then K s s0 else real_zero))).
    - apply Kpos.
    - exact (id_sym Hk0). }
  assert (Hle : real_le (if keep s0 then K s s0 else real_zero) (Z_keep s)).
  { apply (kv_single_le_sum Tok
             (fun y : Tok => if keep y then K s y else real_zero)
             s0 states Hin0).
    intro y. destruct (keep y).
    - apply real_le_from_lt_aux. apply Kpos.
    - apply real_le_refl. }
  destruct Hle as [Hlt | Heq].
  - exact (real_lt_trans real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s) Hlt0 Hlt).
  - exact (real_lt_eq_lt real_zero
             (if keep s0 then K s s0 else real_zero) (Z_keep s) Hlt0 Heq).
Qed.

(* Uniform distribution and the delta-minorization premises (as in the
   UpKVEv.v result contract: delta_minor holds pointwise on the bare K
   and cannot be dropped).  The row-TV and drift statements do not depend
   on the minorization; by the Coq section discipline each Variable
   enters the statements only where it is used. *)
Definition N_R : Real := real_of_nat (length states).
Theorem N_R_pos : real_lt real_zero N_R.
Proof.
  unfold N_R.
  revert states_ne.
  induction states as [| x rest IH]; intro Hne.
  - exact (match Hne (@id_refl _ (@nil Tok)) with end).
  - cbn [length].
    exact (kv_ofnat_S_pos (length rest)).
Qed.
Definition U (s' : Tok) : Real := real_inv_pos N_R N_R_pos.

Variable delta : Real.
Variable delta_pos : real_lt real_zero delta.
Variable delta_le_one : real_le delta real_one.
Variable delta_minor : forall s s' : Tok,
  real_le (real_mult delta (U s')) (K s s').

Definition K_ev (s s' : Tok) : Real :=
  if keep s' then real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s)) else real_zero.

(* ---------- 1. Derived definitions ---------- *)

Definition invZK (s : Tok) : Real := real_inv_pos (Z_keep s) (Z_keep_pos s).

(* Per-row dropped mass and the row total variation *)
Definition tail_row (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => if keep s' then real_zero else K s s') states.
Definition tv_row (s : Tok) : Real :=
  real_list_sum Tok (fun s' : Tok => real_abs (real_minus_r (K s s') (K_ev s s'))) states.

(* Uniform row-error constant (premise of the drift bound; avoids a sup) *)
Variable c : Real.
Variable Hrow : forall s : Tok, real_le (tv_row s) c.

(* Markov step operator and the two-kernel iterations *)
Definition lstep (P : Tok -> Tok -> Real) (mu : Tok -> Real) (s' : Tok) : Real :=
  real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states.

Fixpoint kev_iter (n : nat) (mu : Tok -> Real) : Tok -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => lstep K_ev (kev_iter m mu)
  end.

Fixpoint k_iter (n : nat) (mu : Tok -> Real) : Tok -> Real :=
  match n with
  | 0%nat => mu
  | Datatypes.S m => lstep K (k_iter m mu)
  end.

(* Pointwise-sum total variation (the summed form) *)
Definition Ddist (mu nu : Tok -> Real) : Real :=
  real_list_sum Tok (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states.

(* ---------- 2. Local algebra helpers ---------- *)

(* 0 + a == a (the in-root real_plus_zero states only a + 0 == a) *)
Lemma kv_plus_zero_l : forall a : Real, real_eq (real_plus real_zero a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_plus real_zero a) (real_plus a real_zero) a
           (real_plus_comm real_zero a) (real_plus_zero a)).
Qed.

(* 1·a == a (real_mult_one states the right form a·1 == a; this is the
   left-form bridge) *)
Lemma kv_one_mult_l : forall a : Real, real_eq (real_mult real_one a) a.
Proof.
  intro a.
  exact (real_eq_trans (real_mult real_one a) (real_mult a real_one) a
           (real_mult_comm real_one a) (real_mult_one a)).
Qed.

(* a·(−b) == −(a·b) (symmetry shortcut for real_opp_mult) *)
Lemma kv_opp_mult_bridge : forall a b : Real,
  real_eq (real_mult a (real_opp b)) (real_opp (real_mult a b)).
Proof.
  intros a b. exact (real_eq_sym (real_opp (real_mult a b)) (real_mult a (real_opp b)) (real_opp_mult a b)).
Qed.

(* 2 = 1 + 1 > 0 *)
Lemma kv_two_R_pos : real_lt real_zero (real_plus real_one real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus real_one real_one)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat; exact real_lt_zero_one.
Qed.

(* 3 = 2 + 1 > 0 *)
Lemma kv_three_R_pos : real_lt real_zero
  (real_plus (real_plus real_one real_one) real_one).
Proof.
  apply (RealSetoid.real_lt_id_l real_zero
           (real_plus real_zero real_zero)
           (real_plus (real_plus real_one real_one) real_one)).
  - apply real_eq_sym. apply real_plus_zero.
  - apply real_lt_plus_compat.
    + exact kv_two_R_pos.
    + exact real_lt_zero_one.
Qed.

(* Right distributivity: (a + b)·c == a·c + b·c (real_distrib states the
   left form; bridged through commutativity) *)
Lemma kv_distrib_r : forall a b c0 : Real,
  real_eq (real_mult (real_plus a b) c0)
          (real_plus (real_mult a c0) (real_mult b c0)).
Proof.
  intros a b c0.
  apply (real_eq_trans (real_mult (real_plus a b) c0)
                       (real_mult c0 (real_plus a b)) _).
  - apply real_mult_comm.
  - apply (real_eq_trans (real_mult c0 (real_plus a b))
             (real_plus (real_mult c0 a) (real_mult c0 b)) _).
    + exact (real_distrib c0 a b).
    + apply (RealSetoid.real_eq_plus_compat (real_mult c0 a) (real_mult c0 b)
               (real_mult a c0) (real_mult b c0)
               (real_mult_comm c0 a) (real_mult_comm c0 b)).
Qed.

(* 0 <= a gives |a| == a (real_abs_pos_req in the lt form, plus
   real_abs_zero_req to split the le case) *)
Lemma kv_abs_nonneg_id : forall a : Real,
  real_le real_zero a -> real_eq (real_abs a) a.
Proof.
  intros a H. unfold real_le in H. destruct H as [Hlt | Heq].
  - exact (real_abs_pos_req a Hlt).
  - exact (real_eq_trans (real_abs a) (real_abs real_zero) a
             (real_abs_eq_compat a real_zero (real_eq_sym real_zero a Heq))
             (real_eq_trans (real_abs real_zero) real_zero a
                real_abs_zero_req Heq)).
Qed.

(* Σ (fun _ => 0) == 0 *)
Lemma kv_sum_zero_list : forall (X : Set) (l : list X),
  real_eq (real_list_sum X (fun _ : X => real_zero) l) real_zero.
Proof.
  intros X l. induction l as [| w rest IH].
  - apply real_eq_refl.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_plus real_zero (real_list_sum X (fun _ : X => real_zero) rest))
             (real_plus real_zero real_zero) real_zero).
    + apply (RealSetoid.real_eq_plus_compat real_zero
               (real_list_sum X (fun _ : X => real_zero) rest)
               real_zero real_zero
               (real_eq_refl real_zero) IH).
    + exact (real_eq_trans (real_plus real_zero real_zero) real_zero real_zero
               (real_eq_refl (real_plus real_zero real_zero))
               (real_plus_zero real_zero)).
Qed.

(* The sum of a constant function equals of_nat(|l|)·t (constant sum) *)
Lemma kv_sum_const_list : forall (X : Set) (t : Real) (l : list X),
  real_eq (real_list_sum X (fun _ : X => t) l)
          (real_mult (real_of_nat (length l)) t).
Proof.
  intros X t l. induction l as [| w rest IH].
  - apply (real_eq_sym (real_mult real_zero t) real_zero).
    exact (real_eq_trans (real_mult real_zero t) (real_mult t real_zero) real_zero
             (real_mult_comm real_zero t) (real_mult_zero t)).
  - cbn [real_list_sum length].
    apply (real_eq_trans (real_plus t (real_list_sum X (fun _ : X => t) rest))
             (real_plus (real_mult real_one t)
                        (real_mult (real_of_nat (length rest)) t)) _).
    + apply (RealSetoid.real_eq_plus_compat t
               (real_list_sum X (fun _ : X => t) rest)
               (real_mult real_one t)
               (real_mult (real_of_nat (length rest)) t)
               (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))
               IH).
    + apply real_eq_sym. apply kv_distrib_r.
Qed.

(* t·(inv t·x) == x (general inverse-absorption form; shared by the
   N-average and the eps/3 splitting) *)
Lemma kv_inv_absorb : forall (t : Real) (Ht : real_lt real_zero t) (x : Real),
  real_eq (real_mult t (real_mult (real_inv_pos t Ht) x)) x.
Proof.
  intros t Ht x.
  apply (real_eq_trans (real_mult t (real_mult (real_inv_pos t Ht) x))
                       (real_mult (real_mult t (real_inv_pos t Ht)) x) x).
  - apply real_mult_assoc.
  - apply (real_eq_trans
             (real_mult (real_mult t (real_inv_pos t Ht)) x)
             (real_mult real_one x) x).
    + apply (RealSetoid.real_eq_mult_compat
               (real_mult t (real_inv_pos t Ht)) x real_one x).
      * exact (real_inv_pos_correct t Ht).
      * apply real_eq_refl.
    + apply kv_one_mult_l.
Qed.

(* t + t == (1+1)·t *)
Lemma kv_plus_self_two : forall t : Real,
  real_eq (real_plus t t) (real_mult (real_plus real_one real_one) t).
Proof.
  intro t.
  apply (real_eq_trans
           (real_plus t t)
           (real_plus (real_mult t real_one) (real_mult t real_one))
           (real_mult (real_plus real_one real_one) t)).
  - apply (RealSetoid.real_eq_plus_compat t t (real_mult t real_one)
             (real_mult t real_one)
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))
             (real_eq_sym (real_mult t real_one) t (real_mult_one t))).
  - apply (real_eq_trans
             (real_plus (real_mult t real_one) (real_mult t real_one))
             (real_plus (real_mult real_one t) (real_mult real_one t))
             (real_mult (real_plus real_one real_one) t)).
    + apply (RealSetoid.real_eq_plus_compat (real_mult t real_one)
               (real_mult t real_one) (real_mult real_one t) (real_mult real_one t)
               (real_mult_comm t real_one) (real_mult_comm t real_one)).
    + exact (real_eq_sym _ _ (kv_distrib_r real_one real_one t)).
Qed.

(* (t + t) + t == (2+1)·t *)
Lemma kv_plus_self_three : forall t : Real,
  real_eq (real_plus (real_plus t t) t)
          (real_mult (real_plus (real_plus real_one real_one) real_one) t).
Proof.
  intro t.
  apply (real_eq_trans
           (real_plus (real_plus t t) t)
           (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
                      (real_mult real_one t))
           (real_mult (real_plus (real_plus real_one real_one) real_one) t)).
  - apply (RealSetoid.real_eq_plus_compat (real_plus t t) t
             (real_plus (real_mult real_one t) (real_mult real_one t))
             (real_mult real_one t)
             (RealSetoid.real_eq_plus_compat t t (real_mult real_one t)
                (real_mult real_one t)
                (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))
                (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t)))
             (real_eq_sym (real_mult real_one t) t (kv_one_mult_l t))).
  - exact (real_eq_sym _ _
             (real_eq_trans
                (real_mult (real_plus (real_plus real_one real_one) real_one) t)
                (real_plus (real_mult (real_plus real_one real_one) t)
                           (real_mult real_one t))
                (real_plus (real_plus (real_mult real_one t) (real_mult real_one t))
                           (real_mult real_one t))
                (kv_distrib_r (real_plus real_one real_one) real_one t)
                (RealSetoid.real_eq_plus_compat
                   (real_mult (real_plus real_one real_one) t)
                   (real_mult real_one t)
                   (real_plus (real_mult real_one t) (real_mult real_one t))
                   (real_mult real_one t)
                   (kv_distrib_r real_one real_one t)
                   (real_eq_refl (real_mult real_one t))))).
Qed.


(* |Sum l f| <= Sum l |f| + eps (the Bishop pointwise-eps form; the exact
   triangle |Sum l f| <= Sum l |f| is not available at this Real level --
   only the eps-slack form is provable here, so that form is what this file
   states.  The induction step halves eps; half + half == eps is absorbed
   through inv2.) *)
(* Additive regrouping: (a+(b+h))+h == (a+b)+(h+h) (the structural step
   behind the eps/2 absorption) *)
Lemma kv_merge_regroup : forall a b h : Real,
  real_eq (real_plus (real_plus a (real_plus b h)) h)
          (real_plus (real_plus a b) (real_plus h h)).
Proof.
  intros a b h.
  apply (real_eq_trans
           (real_plus (real_plus a (real_plus b h)) h)
           (real_plus (real_plus (real_plus a b) h) h)
           (real_plus (real_plus a b) (real_plus h h))).
  - apply (RealSetoid.real_eq_plus_compat
             (real_plus a (real_plus b h)) h
             (real_plus (real_plus a b) h) h
             (real_plus_assoc a b h) (real_eq_refl h)).
  - apply (real_eq_sym _ _ (real_plus_assoc (real_plus a b) h h)).
Qed.

Lemma kv_abs_triangle_list_eps : forall (X : Set) (f : X -> Real) (l : list X)
  (eps : Real),
  real_lt real_zero eps ->
  real_le (real_abs (real_list_sum X f l))
          (real_plus (real_list_sum X (fun x : X => real_abs (f x)) l) eps).
Proof.
  intros X f l. induction l as [| w rest IH]; intros eps Heps.
  - apply (real_le_trans
             (real_abs (real_list_sum X f (@nil X))) real_zero
             (real_plus real_zero eps)).
    + apply RealSetoid.real_eq_le. exact real_abs_zero_req.
    + apply real_le_from_lt_aux.
      apply (RealSetoid.real_lt_id_r real_zero eps (real_plus real_zero eps)
               (real_eq_sym _ _ (kv_plus_zero_l eps)) Heps).
  - cbn [real_list_sum].
    assert (Hhalf : real_lt real_zero
              (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                         eps)).
    { apply real_mult_pos_compat.
      - apply real_inv_pos_pos.
      - exact Heps. }
    assert (Hinv2one : real_eq
              (real_plus (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                         (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
              real_one).
    { apply (real_eq_trans
               (real_plus (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
               (real_mult (real_plus real_one real_one)
                          (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))).
      - apply kv_plus_self_two.
      - apply real_inv_pos_correct. }
    assert (Hhh : real_eq
              (real_plus (real_mult (real_inv_pos (real_plus real_one real_one)
                                       kv_two_R_pos) eps)
                         (real_mult (real_inv_pos (real_plus real_one real_one)
                                      kv_two_R_pos) eps))
              eps).
    { apply (real_eq_trans
               (real_plus (real_mult (real_inv_pos (real_plus real_one real_one)
                                        kv_two_R_pos) eps)
                          (real_mult (real_inv_pos (real_plus real_one real_one)
                                       kv_two_R_pos) eps))
               (real_mult
                  (real_plus (real_inv_pos (real_plus real_one real_one)
                               kv_two_R_pos)
                     (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
                  eps)
               eps).
      - apply real_eq_sym. apply kv_distrib_r.
      - apply (real_eq_trans _ _ _
                 (RealSetoid.real_eq_mult_compat
                    (real_plus (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos)
                       (real_inv_pos (real_plus real_one real_one) kv_two_R_pos))
                    eps real_one eps Hinv2one (real_eq_refl eps))
                 (kv_one_mult_l eps)). }
    assert (H1 : real_le
              (real_abs (real_plus (f w) (real_list_sum X f rest)))
              (real_plus (real_plus (real_abs (f w))
                          (real_abs (real_list_sum X f rest)))
                     (real_mult (real_inv_pos (real_plus real_one real_one)
                                  kv_two_R_pos) eps))).
    { exact (real_abs_triangle_le_eps (f w) (real_list_sum X f rest)
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)
               Hhalf). }
    assert (H2 : real_le
              (real_plus (real_plus (real_abs (f w))
                          (real_abs (real_list_sum X f rest)))
                     (real_mult (real_inv_pos (real_plus real_one real_one)
                                  kv_two_R_pos) eps))
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_plus
                       (real_list_sum X (fun x : X => real_abs (f x)) rest)
                       (real_mult (real_inv_pos (real_plus real_one real_one)
                                    kv_two_R_pos) eps)))
                 (real_mult (real_inv_pos (real_plus real_one real_one)
                              kv_two_R_pos) eps))).
    { apply (real_le_plus_compat
               (real_plus (real_abs (f w)) (real_abs (real_list_sum X f rest)))
               (real_plus (real_abs (f w))
                  (real_plus
                     (real_list_sum X (fun x : X => real_abs (f x)) rest)
                     (real_mult (real_inv_pos (real_plus real_one real_one)
                                  kv_two_R_pos) eps)))
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)).
      - apply real_le_plus_compat.
        ++ apply real_le_refl.
        ++ apply IH. exact Hhalf.
      - apply real_le_refl. }
    assert (H3 : real_eq
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_plus
                       (real_list_sum X (fun x : X => real_abs (f x)) rest)
                       (real_mult (real_inv_pos (real_plus real_one real_one)
                                    kv_two_R_pos) eps)))
                 (real_mult (real_inv_pos (real_plus real_one real_one)
                              kv_two_R_pos) eps))
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_list_sum X (fun x : X => real_abs (f x)) rest))
                 (real_plus
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)))).
    { exact (kv_merge_regroup (real_abs (f w))
               (real_list_sum X (fun x : X => real_abs (f x)) rest)
               (real_mult (real_inv_pos (real_plus real_one real_one)
                            kv_two_R_pos) eps)). }
    assert (H4 : real_le
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_list_sum X (fun x : X => real_abs (f x)) rest))
                 (real_plus
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)
                    (real_mult (real_inv_pos (real_plus real_one real_one)
                                 kv_two_R_pos) eps)))
              (real_plus
                 (real_plus (real_abs (f w))
                    (real_list_sum X (fun x : X => real_abs (f x)) rest))
                 eps)).
    { apply (RealSetoid.real_eq_le _ _
               (RealSetoid.real_eq_plus_compat _ _ _ _
                  (real_eq_refl _) Hhh)). }
    apply (real_le_trans _ _ _ H1).
    apply (real_le_trans _ _ _ H2).
    apply (real_le_trans _ _ _ (RealSetoid.real_eq_le _ _ H3)).
    exact H4.
Qed.
(* Double list-sum exchange:
   Sum_{y in l2} Sum_{x in l1} F x y == Sum_{x in l1} Sum_{y in l2} F x y *)
Lemma kv_swap_list : forall (X : Set) (F : X -> X -> Real) (l1 l2 : list X),
  real_eq (real_list_sum X (fun y : X => real_list_sum X (fun x : X => F x y) l1) l2)
          (real_list_sum X (fun x : X => real_list_sum X (fun y : X => F x y) l2) l1).
Proof.
  intros X F l1. induction l1 as [| x l1' IH]; intro l2.
  - cbn [real_list_sum]. apply kv_sum_zero_list.
  - cbn [real_list_sum].
    apply (real_eq_trans
             (real_list_sum X
                (fun y : X => real_plus (F x y)
                           (real_list_sum X (fun x0 : X => F x0 y) l1')) l2)
             (real_plus (real_list_sum X (fun y : X => F x y) l2)
                (real_list_sum X
                   (fun y : X => real_list_sum X (fun x0 : X => F x0 y) l1') l2))
             _).
    + apply real_list_sum_add.
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum X (fun y : X => F x y) l2)
               (real_list_sum X (fun y : X => real_list_sum X (fun x0 : X => F x0 y) l1') l2)
               (real_list_sum X (fun y : X => F x y) l2)
               (real_list_sum X (fun x0 : X => real_list_sum X (fun y : X => F x0 y) l2) l1')
               (real_eq_refl (real_list_sum X (fun y : X => F x y) l2))
               (IH l2)).
Qed.

Lemma kv_share_pos : forall eps : Real,
  real_lt real_zero eps ->
  real_lt real_zero
    (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps).
Proof.
  intros eps Heps. apply real_mult_pos_compat.
  - apply real_inv_pos_pos.
  - exact Heps.
Qed.

(* ---------- 3. tvL (the inv2·Sum|−| isomorphic form; depends on
   kv_two_R_pos, hence the placement after it) ---- *)

Definition tvL (mu nu : Tok -> Real) : Real :=
  real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos) (Ddist mu nu).

(* ---------- 4. World level: Z_keep / tail_row / invZK algebra ---------- *)

(* Z_keep + tail_row == 1 (kept part + dropped part == whole row == 1) *)
Lemma kv_ZK_plus_tail : forall s : Tok,
  real_eq (real_plus (Z_keep s) (tail_row s)) real_one.
Proof.
  intro s.
  apply (real_eq_trans
           (real_plus (Z_keep s) (tail_row s))
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus (if keep s' then K s s' else real_zero)
                           (if keep s' then real_zero else K s s')) states)
           real_one).
  - apply (real_eq_trans
             (real_plus (Z_keep s) (tail_row s))
             (real_plus
                (real_list_sum Tok
                   (fun s' : Tok => if keep s' then K s s' else real_zero) states)
                (real_list_sum Tok
                   (fun s' : Tok => if keep s' then real_zero else K s s') states))
             _).
    + apply real_eq_refl.
    + apply real_eq_sym. apply real_list_sum_add.
  - apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus (if keep s' then K s s' else real_zero)
                             (if keep s' then real_zero else K s s')) states)
             (real_list_sum Tok (fun s' : Tok => K s s') states)
             real_one).
    + apply real_list_sum_ext. intro w. destruct (keep w).
      * apply real_plus_zero.
      * apply kv_plus_zero_l.
    + exact (Krow s).
Qed.
(* tail_row == 1 − Z_keep (reshaped from Z + tail == 1) *)
Lemma kv_tail_one_minus : forall s : Tok,
  real_eq (tail_row s) (real_minus_r real_one (Z_keep s)).
Proof.
  intro s.
  assert (Hzt : real_eq (real_plus (Z_keep s) (tail_row s)) real_one)
    by exact (kv_ZK_plus_tail s).
  apply real_eq_sym.
  apply (real_eq_trans (real_minus_r real_one (Z_keep s))
           (real_minus_r (real_plus (Z_keep s) (tail_row s)) (Z_keep s))
           (tail_row s)).
  - unfold real_minus_r.
    apply (real_eq_trans
             (real_plus real_one (real_opp (Z_keep s)))
             (real_plus (real_plus (Z_keep s) (tail_row s)) (real_opp (Z_keep s)))
             _).
    + apply (RealSetoid.real_eq_plus_compat real_one (real_opp (Z_keep s))
               (real_plus (Z_keep s) (tail_row s)) (real_opp (Z_keep s))
               (real_eq_sym (real_plus (Z_keep s) (tail_row s)) real_one Hzt)
               (real_eq_refl _)).
    + apply real_eq_refl.
  - unfold real_minus_r.
    assert (Hs1 : real_eq
               (real_plus (real_plus (Z_keep s) (tail_row s)) (real_opp (Z_keep s)))
               (real_plus (Z_keep s) (real_plus (tail_row s) (real_opp (Z_keep s))))).
    { apply real_eq_sym. apply real_plus_assoc. }
    assert (Hs2 : real_eq
               (real_plus (Z_keep s) (real_plus (tail_row s) (real_opp (Z_keep s))))
               (real_plus (Z_keep s) (real_plus (real_opp (Z_keep s)) (tail_row s)))).
    { apply (RealSetoid.real_eq_plus_compat _ _ _ _
               (real_eq_refl _) (real_plus_comm _ _)). }
    assert (Hs3 : real_eq
               (real_plus (Z_keep s) (real_plus (real_opp (Z_keep s)) (tail_row s)))
               (real_plus (real_plus (Z_keep s) (real_opp (Z_keep s))) (tail_row s))).
    { apply real_plus_assoc. }
    assert (Hs4 : real_eq
               (real_plus (real_plus (Z_keep s) (real_opp (Z_keep s))) (tail_row s))
               (real_plus real_zero (tail_row s))).
    { apply (RealSetoid.real_eq_plus_compat
               (real_plus (Z_keep s) (real_opp (Z_keep s))) (tail_row s)
               real_zero (tail_row s)
               (real_plus_opp (Z_keep s)) (real_eq_refl _)). }
    apply (real_eq_trans _ _ _ Hs1
             (real_eq_trans _ _ _ Hs2
                (real_eq_trans _ _ _ Hs3
                   (real_eq_trans _ _ _ Hs4 (kv_plus_zero_l _))))).
Qed.
(* Pointwise sign-certificate identity (summed right-hand side):
   |K − K_ev| == (if keep then K_ev − K else 0) + (if keep then 0 else K).
   The kept branch uses real_abs_minus_r_nonneg_aux (the sign certificate
   K <= K_ev); on the dropped branch |K−0| == K *)

Lemma kv_ZK_le_one : forall s : Tok, real_le (Z_keep s) real_one.
Proof.
  intro s.
  apply (real_le_trans (Z_keep s)
           (real_list_sum Tok (fun s' : Tok => K s s') states) real_one).
  - unfold Z_keep. apply real_list_sum_le. intro w. destruct (keep w).
    + apply real_le_refl.
    + apply real_le_from_lt_aux. apply Kpos.
  - apply RealSetoid.real_eq_le. exact (Krow s).
Qed.

(* invZK >= 1 (Z <= 1 with the order-reversing inverse, plus inv(1) == 1) *)
Lemma kv_invZ_ge_one : forall s : Tok, real_le real_one (invZK s).
Proof.
  intro s.
  apply (RealSetoid.real_le_id_l real_one
           (real_inv_pos real_one real_lt_zero_one) (invZK s)).
  - apply (real_eq_sym _ _
             (real_eq_trans (real_inv_pos real_one real_lt_zero_one)
                (real_mult real_one (real_inv_pos real_one real_lt_zero_one))
                real_one
                (real_eq_sym _ _ (kv_one_mult_l
                   (real_inv_pos real_one real_lt_zero_one)))
                (real_inv_pos_correct real_one real_lt_zero_one))).
  - exact (real_inv_pos_le_compat (Z_keep s) real_one
             (Z_keep_pos s) real_lt_zero_one (kv_ZK_le_one s)).
Qed.

(* Kept-branch sign certificate (scaled form): K <= K·invZ
   (1 <= invZ, and left multiplication preserves the order) *)
Lemma kv_K_le_Kev_scaled : forall s s' : Tok,
  real_le (K s s') (real_mult (K s s') (invZK s)).
Proof.
  intros s s'.
  apply (real_le_trans _ (real_mult (K s s') real_one) _).
  - apply RealSetoid.real_eq_le. apply real_eq_sym. apply real_mult_one.
  - exact (real_le_mult_compat_l_aux real_one (invZK s) (K s s')
             (Kpos s s') (kv_invZ_ge_one s)).
Qed.

(* Pointwise extensionality: the K_ev summand == (if keep then K else
   0)·invZ (used for the row normalization) *)
Lemma kv_summand_eq : forall (s w : Tok),
  real_eq
    (if keep w
     then real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s))
     else real_zero)
    (real_mult (if keep w then K s w else real_zero)
               (real_inv_pos (Z_keep s) (Z_keep_pos s))).
Proof.
  intros s w. destruct (keep w).
  - apply real_eq_refl.
  - apply (real_eq_sym (real_mult real_zero
                          (real_inv_pos (Z_keep s) (Z_keep_pos s))) real_zero
             (real_eq_trans
                (real_mult real_zero (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) real_zero)
                real_zero
                (real_mult_comm real_zero
                   (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                (real_mult_zero (real_inv_pos (Z_keep s) (Z_keep_pos s))))).
Qed.

(* Multiplicative pointwise form:
   (if keep then K_ev−K else 0) == (if keep then K else 0)·(invZ−1) *)
Lemma kv_summand_scaled : forall (s w : Tok),
  real_eq
    (if keep w then real_minus_r (K_ev s w) (K s w) else real_zero)
    (real_mult (if keep w then K s w else real_zero)
               (real_minus_r (invZK s) real_one)).
Proof.
  intros s w. unfold K_ev. destruct (keep w).
  - (* Kept branch: (K·invZ) + (−K) == K·(invZ + (−1)), via the
       −K == K·(−1) bridge and the symmetric distributivity *)
    apply (real_eq_trans
             (real_minus_r
                (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                (K s w))
             (real_plus
                (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                (real_opp (K s w)))
             (real_mult (K s w) (real_minus_r (invZK s) real_one))).
    + apply real_eq_refl.
    + apply (real_eq_trans
                (real_plus
                   (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                   (real_opp (K s w)))
                (real_plus
                   (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                   (real_mult (K s w) (real_opp real_one)))
                (real_mult (K s w) (real_minus_r (invZK s) real_one))).
      * apply (RealSetoid.real_eq_plus_compat
                  (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                  (real_opp (K s w))
                  (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                  (real_mult (K s w) (real_opp real_one))
                  (real_eq_refl _)
                  (real_eq_trans (real_opp (K s w))
                     (real_opp (real_mult (K s w) real_one))
                     (real_mult (K s w) (real_opp real_one))
                     (RealSetoid.real_eq_opp_compat (K s w)
                        (real_mult (K s w) real_one)
                        (real_eq_sym (real_mult (K s w) real_one) (K s w)
                           (real_mult_one (K s w))))
                     (real_opp_mult (K s w) real_one))).
      * apply real_eq_sym.
        exact (real_distrib (K s w)
                 (real_inv_pos (Z_keep s) (Z_keep_pos s)) (real_opp real_one)).
  - (* Dropped branch: 0 == 0·(invZ−1) (real_eq_sym at the argument
       position: the conclusion reads real_eq y x) *)
    apply (real_eq_sym (real_mult real_zero (real_minus_r (invZK s) real_one))
              real_zero
              (real_eq_trans
                 (real_mult real_zero (real_minus_r (invZK s) real_one))
                 (real_mult (real_minus_r (invZK s) real_one) real_zero)
                 real_zero
                 (real_mult_comm real_zero (real_minus_r (invZK s) real_one))
                 (real_mult_zero (real_minus_r (invZK s) real_one)))).
Qed.

(* K_ev row normalization: Sum_{s'} K_ev(s,s') == 1 (serves as the
   normalization premise of the drift induction) *)
Lemma kv_kev_row_one : forall s : Tok,
  real_eq (real_list_sum Tok (K_ev s) states) real_one.
Proof.
  intro s. unfold K_ev.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun w : Tok =>
                 (if keep w
                  then real_mult (K s w)
                       (real_inv_pos (Z_keep s) (Z_keep_pos s))
                  else real_zero)) states)
           (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) (Z_keep s))
           real_one).
  - apply (real_eq_trans _ _ _
             (real_list_sum_ext Tok
                (fun w : Tok =>
                   (if keep w
                    then real_mult (K s w)
                         (real_inv_pos (Z_keep s) (Z_keep_pos s))
                    else real_zero))
                (fun w : Tok =>
                   real_mult (if keep w then K s w else real_zero)
                             (real_inv_pos (Z_keep s) (Z_keep_pos s))) states
                (kv_summand_eq s))
             (real_list_sum_linear_r Tok
                (real_inv_pos (Z_keep s) (Z_keep_pos s))
                (fun w : Tok => if keep w then K s w else real_zero) states)).
  - apply (real_eq_trans
              (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) (Z_keep s))
              (real_mult (Z_keep s) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
              real_one).
    + apply real_mult_comm.
    + exact (real_inv_pos_correct (Z_keep s) (Z_keep_pos s)).
Qed.

(* Scaling of the kept-branch sum: Sum_keep(K_ev − K) == (invZ − 1)·Z_keep
   (pointwise kv_summand_scaled, closed with real_list_sum_linear_r) *)
Lemma kv_gsum_scaled : forall s : Tok,
  real_eq
    (real_list_sum Tok
       (fun s' : Tok =>
          if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
       states)
    (real_mult (real_minus_r (invZK s) real_one) (Z_keep s)).
Proof.
  intro s.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
              states)
           (real_list_sum Tok
              (fun w : Tok =>
                 real_mult (if keep w then K s w else real_zero)
                           (real_minus_r (invZK s) real_one))
              states)
           (real_mult (real_minus_r (invZK s) real_one) (Z_keep s))).
  - apply real_list_sum_ext. intro w. apply kv_summand_scaled.
  - apply (real_list_sum_linear_r Tok
              (real_minus_r (invZK s) real_one)
              (fun w : Tok => if keep w then K s w else real_zero) states).
Qed.

(* (invZ − 1)·Z_keep == 1 − Z_keep == tail_row (kv_distrib_r with the
   real_inv_pos_correct and opposite bridges, closed by
   kv_tail_one_minus) *)
Lemma kv_scaledZ_tail : forall s : Tok,
  real_eq (real_mult (real_minus_r (invZK s) real_one) (Z_keep s)) (tail_row s).
Proof.
  intro s.
  apply (real_eq_trans
           (real_mult (real_minus_r (invZK s) real_one) (Z_keep s))
           (real_minus_r real_one (Z_keep s))
           (tail_row s)).
  - apply (real_eq_trans
              (real_mult (real_minus_r (invZK s) real_one) (Z_keep s))
              (real_plus (real_mult (invZK s) (Z_keep s))
                         (real_mult (real_opp real_one) (Z_keep s)))
              (real_minus_r real_one (Z_keep s))).
    + apply (kv_distrib_r (invZK s) (real_opp real_one) (Z_keep s)).
    + apply (RealSetoid.real_eq_plus_compat
               (real_mult (invZK s) (Z_keep s))
               (real_mult (real_opp real_one) (Z_keep s))
               real_one (real_opp (Z_keep s))
               (real_eq_trans (real_mult (invZK s) (Z_keep s))
                  (real_mult (Z_keep s) (invZK s)) real_one
                  (real_mult_comm (invZK s) (Z_keep s))
                  (real_inv_pos_correct (Z_keep s) (Z_keep_pos s)))
               (real_eq_trans (real_mult (real_opp real_one) (Z_keep s))
                  (real_opp (real_mult real_one (Z_keep s)))
                  (real_opp (Z_keep s))
                  (real_eq_sym _ _ (real_opp_mult_r real_one (Z_keep s)))
                  (RealSetoid.real_eq_opp_compat (real_mult real_one (Z_keep s))
                     (Z_keep s) (kv_one_mult_l (Z_keep s))))).
  - exact (real_eq_sym _ _ (kv_tail_one_minus s)).
Qed.

(* Pointwise sign certificate: |K − K_ev| == if keep then K_ev − K else K
   (kept branch by real_abs_minus_r_nonneg_aux; dropped branch through
   the −0, add-zero and |K| = K bridges) *)
Lemma kv_tvrow_pointwise : forall s w : Tok,
  real_eq (real_abs (real_minus_r (K s w) (K_ev s w)))
          (if keep w then real_minus_r (K_ev s w) (K s w) else K s w).
Proof.
  intros s w. unfold K_ev. destruct (keep w).
  - exact (real_abs_minus_r_nonneg_aux (K s w)
             (real_mult (K s w) (real_inv_pos (Z_keep s) (Z_keep_pos s)))
             (kv_K_le_Kev_scaled s w)).
  - apply (real_eq_trans
             (real_abs (real_plus (K s w) (real_opp real_zero)))
             (real_abs (K s w)) (K s w)).
    + apply real_abs_eq_compat.
      apply (real_eq_trans
               (real_plus (K s w) (real_opp real_zero))
               (real_plus (K s w) real_zero) (K s w)).
      * apply (RealSetoid.real_eq_plus_compat (K s w) (real_opp real_zero)
                 (K s w) real_zero (real_eq_refl _) real_opp_zero).
      * apply real_plus_zero.
    + exact (kv_abs_nonneg_id (K s w)
               (real_le_from_lt_aux real_zero (K s w) (Kpos s w))).
Qed.

(* Splitting: tv_row == Sum_keep(K_ev−K) + Sum_drop K (pointwise
   certificate by extensionality, terms reassembled by ext/add) *)
Lemma kv_tvrow_split : forall s : Tok,
  real_eq (tv_row s)
          (real_plus
             (real_list_sum Tok
                (fun s' : Tok =>
                   if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
                states)
             (tail_row s)).
Proof.
  intro s. unfold tv_row.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (K s s') (K_ev s s'))) states)
           (real_plus
              (real_list_sum Tok
                 (fun w : Tok =>
                    if keep w then real_minus_r (K_ev s w) (K s w) else real_zero)
                 states)
              (real_list_sum Tok
                 (fun w : Tok => if keep w then real_zero else K s w)
                 states))
           (real_plus
              (real_list_sum Tok
                 (fun s' : Tok =>
                    if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
                 states)
              (tail_row s))).
  - apply (real_eq_trans
              (real_list_sum Tok
                 (fun s' : Tok =>
                    real_abs (real_minus_r (K s s') (K_ev s s'))) states)
              (real_list_sum Tok
                 (fun w : Tok =>
                    if keep w then real_minus_r (K_ev s w) (K s w) else K s w)
                 states)
              (real_plus
                 (real_list_sum Tok
                    (fun w : Tok =>
                       if keep w then real_minus_r (K_ev s w) (K s w) else real_zero)
                    states)
                 (real_list_sum Tok
                    (fun w : Tok => if keep w then real_zero else K s w)
                    states))).
    + apply real_list_sum_ext. exact (kv_tvrow_pointwise s).
    + apply (real_eq_trans
                (real_list_sum Tok
                   (fun w : Tok =>
                      if keep w then real_minus_r (K_ev s w) (K s w) else K s w)
                   states)
                (real_list_sum Tok
                   (fun w : Tok =>
                      real_plus
                        (if keep w then real_minus_r (K_ev s w) (K s w)
                         else real_zero)
                        (if keep w then real_zero else K s w))
                   states)
                (real_plus
                   (real_list_sum Tok
                      (fun w : Tok =>
                         if keep w then real_minus_r (K_ev s w) (K s w)
                         else real_zero)
                      states)
                   (real_list_sum Tok
                      (fun w : Tok => if keep w then real_zero else K s w)
                      states))).
      * apply real_list_sum_ext. intro w. destruct (keep w).
        -- apply real_eq_sym. apply real_plus_zero.
        -- apply real_eq_sym. apply kv_plus_zero_l.
      * apply real_list_sum_add.
  - apply real_eq_refl.
Qed.

(* ================== Row-TV main result: the exact identity ==============
   tv_row(s) == tail_row(s) + tail_row(s) (== 2·tail_row == 2·(1 − Z_keep)) *)
Theorem kev_row_tv_exact : forall s : Tok,
  real_eq (tv_row s) (real_plus (tail_row s) (tail_row s)).
Proof.
  intro s.
  apply (real_eq_trans (tv_row s)
           (real_plus
              (real_list_sum Tok
                 (fun s' : Tok =>
                    if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
                 states)
              (tail_row s))
           (real_plus (tail_row s) (tail_row s))).
  - exact (kv_tvrow_split s).
  - apply (RealSetoid.real_eq_plus_compat
             (real_list_sum Tok
                (fun s' : Tok =>
                   if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
                states)
             (tail_row s)
             (tail_row s) (tail_row s)
             (real_eq_trans
                (real_list_sum Tok
                   (fun s' : Tok =>
                      if keep s' then real_minus_r (K_ev s s') (K s s') else real_zero)
                   states)
                (real_mult (real_minus_r (invZK s) real_one) (Z_keep s))
                (tail_row s)
                (kv_gsum_scaled s) (kv_scaledZ_tail s))
             (real_eq_refl _)).
Qed.

(* The <= 2·tail form (companion result of the exact identity; real_le is
   a Type-level encoding, with no Prop leakage) *)
Corollary kev_row_tv_bound : forall s : Tok,
  real_le (tv_row s) (real_plus (tail_row s) (tail_row s)).
Proof.
  intro s. apply RealSetoid.real_eq_le. exact (kev_row_tv_exact s).
Qed.

(* Paper form: tv_row == 2·(1 − Z_keep) *)
Corollary kev_row_tv_one_minus_Z : forall s : Tok,
  real_eq (tv_row s)
          (real_mult (real_plus real_one real_one)
                     (real_minus_r real_one (Z_keep s))).
Proof.
  intro s.
  apply (real_eq_trans (tv_row s)
           (real_mult (real_plus real_one real_one) (tail_row s)) _).
  - apply (real_eq_trans (tv_row s) (real_plus (tail_row s) (tail_row s)) _).
    + exact (kev_row_tv_exact s).
    + apply kv_plus_self_two.
  - apply (RealSetoid.real_eq_mult_compat
             (real_plus real_one real_one) (tail_row s)
             (real_plus real_one real_one) (real_minus_r real_one (Z_keep s))
             (real_eq_refl _) (kv_tail_one_minus s)).
Qed.

(* ---------- Drift machinery: step-operator algebra ---------- *)

(* Step-difference identity (same kernel):
   Pμ(s') − Pν(s') == Sum_s (μ−ν)(s)·P(s,s') *)
Lemma kv_lstep_minus_pt2 : forall (P : Tok -> Tok -> Real) (mu nu : Tok -> Real)
  (s' : Tok),
  real_eq (real_minus_r (lstep P mu s') (lstep P nu s'))
          (real_list_sum Tok
             (fun s : Tok => real_mult (real_minus_r (mu s) (nu s)) (P s s')) states).
Proof.
  intros P mu nu s'. unfold lstep, real_minus_r.
  apply (real_eq_trans
           (real_plus
              (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
              (real_opp
                 (real_list_sum Tok (fun s : Tok => real_mult (nu s) (P s s')) states)))
           (real_list_sum Tok
              (fun s : Tok =>
                 real_plus (real_mult (mu s) (P s s'))
                           (real_opp (real_mult (nu s) (P s s')))) states)
           _).
  - apply (real_eq_trans
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
                (real_opp
                   (real_list_sum Tok (fun s : Tok => real_mult (nu s) (P s s')) states)))
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
                (real_list_sum Tok
                   (fun s : Tok => real_opp (real_mult (nu s) (P s s'))) states))
             _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
               (real_opp
                  (real_list_sum Tok (fun s : Tok => real_mult (nu s) (P s s')) states))
               (real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
               (real_list_sum Tok
                  (fun s : Tok => real_opp (real_mult (nu s) (P s s'))) states)
               (real_eq_refl _)
               (real_eq_sym _ _
                  (real_list_sum_opp Tok (fun s : Tok => real_mult (nu s) (P s s')) states))).
    + apply real_eq_sym. apply real_list_sum_add.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_plus (real_mult (mu s) (P s s'))
                        (real_opp (real_mult (nu s) (P s s'))))
             (real_plus (real_mult (mu s) (P s s'))
                        (real_mult (real_opp (nu s)) (P s s'))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (mu s) (P s s'))
               (real_opp (real_mult (nu s) (P s s')))
               (real_mult (mu s) (P s s'))
               (real_mult (real_opp (nu s)) (P s s'))
               (real_eq_refl _)
               (real_opp_mult_r (nu s) (P s s'))).
    + apply real_eq_sym. apply kv_distrib_r.
Qed.

(* Two-kernel step-difference identity (same weight w):
   Sum_s w(s)·P(s,s') − Sum_s w(s)·Q(s,s') == Sum_s w(s)·(P−Q)(s,s') *)
Lemma kv_lstep2_minus_pt : forall (P Q : Tok -> Tok -> Real) (w : Tok -> Real)
  (s' : Tok),
  real_eq (real_minus_r (lstep P w s') (lstep Q w s'))
          (real_list_sum Tok
             (fun s : Tok =>
                real_mult (w s) (real_minus_r (P s s') (Q s s'))) states).
Proof.
  intros P Q w s'. unfold lstep, real_minus_r.
  apply (real_eq_trans
           (real_plus
              (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
              (real_opp
                 (real_list_sum Tok (fun s : Tok => real_mult (w s) (Q s s')) states)))
           (real_list_sum Tok
              (fun s : Tok =>
                 real_plus (real_mult (w s) (P s s'))
                           (real_opp (real_mult (w s) (Q s s')))) states)
           _).
  - apply (real_eq_trans
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
                (real_opp
                   (real_list_sum Tok (fun s : Tok => real_mult (w s) (Q s s')) states)))
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
                (real_list_sum Tok
                   (fun s : Tok => real_opp (real_mult (w s) (Q s s'))) states))
             _).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
               (real_opp
                  (real_list_sum Tok (fun s : Tok => real_mult (w s) (Q s s')) states))
               (real_list_sum Tok (fun s : Tok => real_mult (w s) (P s s')) states)
               (real_list_sum Tok
                  (fun s : Tok => real_opp (real_mult (w s) (Q s s'))) states)
               (real_eq_refl _)
               (real_eq_sym _ _
                  (real_list_sum_opp Tok (fun s : Tok => real_mult (w s) (Q s s')) states))).
    + apply real_eq_sym. apply real_list_sum_add.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_plus (real_mult (w s) (P s s'))
                        (real_opp (real_mult (w s) (Q s s'))))
             (real_plus (real_mult (w s) (P s s'))
                        (real_mult (w s) (real_opp (Q s s')))) _).
    + apply (RealSetoid.real_eq_plus_compat (real_mult (w s) (P s s'))
               (real_opp (real_mult (w s) (Q s s')))
               (real_mult (w s) (P s s'))
               (real_mult (w s) (real_opp (Q s s')))
               (real_eq_refl _)
               (real_eq_sym _ _ (real_mult_opp_l (w s) (Q s s')))).
    + apply real_eq_sym. apply real_distrib.
Qed.

(* D(μ,μ) == 0 *)
Lemma kv_D_zero : forall mu : Tok -> Real, real_eq (Ddist mu mu) real_zero.
Proof.
  intro mu. unfold Ddist.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun x : Tok => real_abs (real_minus_r (mu x) (mu x))) states)
           (real_list_sum Tok (fun x : Tok => real_zero) states) real_zero).
  - apply real_list_sum_ext. intro x.
    apply (real_eq_trans (real_abs (real_minus_r (mu x) (mu x)))
             (real_abs real_zero) real_zero).
    + apply real_abs_eq_compat. apply real_plus_opp.
    + exact real_abs_zero_req.
  - apply kv_sum_zero_list.
Qed.

(* A Markov step preserves the total mass *)
Lemma kv_lstep_norm : forall (P : Tok -> Tok -> Real),
  (forall s : Tok, real_eq (real_list_sum Tok (P s) states) real_one) ->
  forall mu : Tok -> Real,
  real_eq (real_list_sum Tok (fun s' : Tok => lstep P mu s') states)
          (real_list_sum Tok mu states).
Proof.
  intros P HP mu. unfold lstep.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_list_sum Tok (fun s : Tok => real_mult (mu s) (P s s')) states)
              states)
           (real_list_sum Tok
              (fun s : Tok =>
                 real_list_sum Tok (fun s' : Tok => real_mult (mu s) (P s s')) states)
              states)
           (real_list_sum Tok mu states)).
  - apply kv_swap_list.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_list_sum Tok (fun s' : Tok => real_mult (mu s) (P s s')) states)
             (real_mult (mu s) (real_list_sum Tok (P s) states)) (mu s)).
    + apply real_list_sum_linear.
    + apply (real_eq_trans
               (real_mult (mu s) (real_list_sum Tok (P s) states))
               (real_mult (mu s) real_one) (mu s)).
      * apply (RealSetoid.real_eq_mult_compat (mu s)
                 (real_list_sum Tok (P s) states) (mu s) real_one
                 (real_eq_refl (mu s)) (HP s)).
      * apply real_mult_one.
Qed.

(* The step operator is nonnegative (mu >= 0 and P >= 0) *)
Lemma kv_lstep_nonneg : forall (P : Tok -> Tok -> Real),
  (forall s s' : Tok, real_le real_zero (P s s')) ->
  forall mu : Tok -> Real,
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall s' : Tok, real_le real_zero (lstep P mu s').
Proof.
  intros P HP mu Hmu s'. unfold lstep.
  apply real_list_sum_nonneg. intro s.
  apply (RealSetoid.real_le_id_l real_zero
           (real_mult real_zero (P s s')) (real_mult (mu s) (P s s'))).
  - apply (real_eq_sym (real_mult real_zero (P s s')) real_zero).
    exact (real_eq_trans (real_mult real_zero (P s s'))
             (real_mult (P s s') real_zero) real_zero
             (real_mult_comm real_zero (P s s')) (real_mult_zero (P s s'))).
  - exact (real_le_mult_compat_weak real_zero (mu s) (P s s') (HP s s') (Hmu s)).
Qed.

(* K_ev >= 0 (nonnegativity of the contract kernel) *)
Lemma kv_K_ev_nonneg : forall s s' : Tok, real_le real_zero (K_ev s s').
Proof.
  intros s s'. unfold K_ev. destruct (keep s').
  - apply (RealSetoid.real_le_id_l real_zero
             (real_mult real_zero (real_inv_pos (Z_keep s) (Z_keep_pos s)))
             (real_mult (K s s') (real_inv_pos (Z_keep s) (Z_keep_pos s)))).
    + apply (real_eq_sym (real_mult real_zero (real_inv_pos (Z_keep s) (Z_keep_pos s)))
               real_zero).
      exact (real_eq_trans
                (real_mult real_zero (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                (real_mult (real_inv_pos (Z_keep s) (Z_keep_pos s)) real_zero)
                real_zero
                (real_mult_comm real_zero (real_inv_pos (Z_keep s) (Z_keep_pos s)))
                (real_mult_zero (real_inv_pos (Z_keep s) (Z_keep_pos s)))).
    + exact (real_le_mult_compat_weak real_zero (K s s')
               (real_inv_pos (Z_keep s) (Z_keep_pos s))
               (real_le_from_lt_aux real_zero
                  (real_inv_pos (Z_keep s) (Z_keep_pos s))
                  (real_inv_pos_pos (Z_keep s) (Z_keep_pos s)))
               (real_le_from_lt_aux real_zero (K s s') (Kpos s s'))).
  - apply real_le_refl.
Qed.

(* Normalization and nonnegativity of the iterations *)
Lemma kv_kev_iter_norm : forall (n : nat) (mu : Tok -> Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  real_eq (real_list_sum Tok (kev_iter n mu) states) real_one.
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu.
  - exact Hmu.
  - exact (real_eq_trans _ _ _
             (kv_lstep_norm K_ev (fun s : Tok => kv_kev_row_one s) (kev_iter n mu))
             (IH mu Hmu)).
Qed.

Lemma kv_k_iter_norm : forall (n : nat) (mu : Tok -> Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  real_eq (real_list_sum Tok (k_iter n mu) states) real_one.
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu.
  - exact Hmu.
  - exact (real_eq_trans _ _ _
             (kv_lstep_norm K Krow (k_iter n mu))
             (IH mu Hmu)).
Qed.

Lemma kv_kev_iter_nonneg : forall (n : nat) (mu : Tok -> Real),
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall s : Tok, real_le real_zero (kev_iter n mu s).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu s'.
  - exact (Hmu s').
  - exact (kv_lstep_nonneg K_ev kv_K_ev_nonneg (kev_iter n mu) (IH mu Hmu) s').
Qed.

Lemma kv_k_iter_nonneg : forall (n : nat) (mu : Tok -> Real),
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall s : Tok, real_le real_zero (k_iter n mu s).
Proof.
  intro n. induction n as [| n IH]; intros mu Hmu s'.
  - exact (Hmu s').
  - exact (kv_lstep_nonneg K
             (fun s s' : Tok => real_le_from_lt_aux real_zero (K s s') (Kpos s s'))
             (k_iter n mu) (IH mu Hmu) s').
Qed.

(* Double-sum reduction of D(mu,nu):
   Sum_s' Sum_s |(μ−ν)(s)·P(s,s')| == Sum_s |μ(s)−ν(s)|
   (kv_swap_list exchange, pointwise abs-mult product splitting,
   row-normalization absorption) *)
Lemma kv_dsum_abs_eq : forall (P : Tok -> Tok -> Real),
  (forall s s' : Tok, real_le real_zero (P s s')) ->
  (forall s : Tok, real_eq (real_list_sum Tok (P s) states) real_one) ->
  forall mu nu : Tok -> Real,
  real_eq (real_list_sum Tok
             (fun s' : Tok =>
                real_list_sum Tok
                  (fun s : Tok =>
                     real_abs (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                  states)
              states)
          (real_list_sum Tok
             (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states).
Proof.
  intros P Hnn HP mu nu.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                   states)
              states)
           (real_list_sum Tok
              (fun s : Tok =>
                 real_list_sum Tok
                   (fun s' : Tok =>
                      real_abs
                        (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                   states)
              states) _).
  - apply kv_swap_list.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_abs
                     (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                states)
             (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                        (real_list_sum Tok (P s) states)) _).
    + apply (real_eq_trans
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_abs
                       (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                  states)
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_mult (real_abs (real_minus_r (mu s) (nu s)))
                               (P s s'))
                  states) _).
      * apply real_list_sum_ext. intro s'.
        apply (real_eq_trans
                 (real_abs
                    (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                 (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                            (real_abs (P s s')))
                 (real_mult (real_abs (real_minus_r (mu s) (nu s)))
                            (P s s'))).
        -- exact (real_abs_mult_req (real_minus_r (mu s) (nu s)) (P s s')).
        -- apply (RealSetoid.real_eq_mult_compat
                    (real_abs (real_minus_r (mu s) (nu s)))
                    (real_abs (P s s'))
                    (real_abs (real_minus_r (mu s) (nu s)))
                    (P s s')
                    (real_eq_refl _)
                    (kv_abs_nonneg_id (P s s') (Hnn s s'))).
      * apply real_list_sum_linear.
    + exact (real_eq_trans _ _ _
               (RealSetoid.real_eq_mult_compat
                  (real_abs (real_minus_r (mu s) (nu s)))
                  (real_list_sum Tok (P s) states)
                  (real_abs (real_minus_r (mu s) (nu s))) real_one
                  (real_eq_refl _) (HP s))
               (real_mult_one (real_abs (real_minus_r (mu s) (nu s))))).
Qed.

(* TV non-expansiveness of a Markov kernel (the Bishop eps form):
   D(Pμ, Pν) <= D(μ,ν) + ε (row triangle, double-sum exchange,
   row-normalization absorption) *)
Lemma kv_nonexpansive : forall (P : Tok -> Tok -> Real),
  (forall s : Tok, real_eq (real_list_sum Tok (P s) states) real_one) ->
  (forall s s' : Tok, real_le real_zero (P s s')) ->
  forall mu nu : Tok -> Real, forall eps : Real,
  real_lt real_zero eps ->
  real_le (Ddist (lstep P mu) (lstep P nu)) (real_plus (Ddist mu nu) eps).
Proof.
  intros P HP Hnn mu nu eps Heps.
  assert (Hshare : real_lt real_zero
            (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps))
    by (apply kv_share_pos; exact Heps).
  unfold Ddist.
  apply (real_le_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (lstep P mu s') (lstep P nu s'))) states)
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_abs
                           (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                      states)
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps))
              states)
           (real_plus
              (real_list_sum Tok
                 (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states)
              eps)).
  - apply real_list_sum_le. intro s'.
    apply (real_le_trans
             (real_abs (real_minus_r (lstep P mu s') (lstep P nu s')))
             (real_abs
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (real_minus_r (mu s) (nu s)) (P s s')) states))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (real_minus_r (mu s) (nu s)) (P s s'))) states)
                (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                           eps))).
    + apply inr. apply real_abs_eq_compat. exact (kv_lstep_minus_pt2 P mu nu s').
    + exact (kv_abs_triangle_list_eps Tok
               (fun s : Tok => real_mult (real_minus_r (mu s) (nu s)) (P s s'))
               states _ Hshare).
  - apply inr.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_abs
                             (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                        states)
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                states)
             (real_plus
                (real_list_sum Tok
                   (fun s' : Tok =>
                      real_list_sum Tok
                        (fun s : Tok =>
                           real_abs
                             (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                        states)
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps)))
             (real_plus
                (real_list_sum Tok
                   (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states)
                eps)).
    + apply (real_eq_trans _ _ _
               (real_list_sum_add Tok
                  (fun s : Tok =>
                     real_list_sum Tok
                       (fun s0 : Tok =>
                          real_abs
                            (real_mult (real_minus_r (mu s0) (nu s0)) (P s0 s)))
                       states)
                  (fun _ : Tok =>
                     real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                               eps)
                  states)
               (RealSetoid.real_eq_plus_compat
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_list_sum Tok
                          (fun s0 : Tok =>
                             real_abs
                               (real_mult (real_minus_r (mu s0) (nu s0)) (P s0 s)))
                          states)
                      states)
                  (real_list_sum Tok
                     (fun _ : Tok =>
                        real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                  eps)
                     states)
                  (real_list_sum Tok
                     (fun s : Tok =>
                        real_list_sum Tok
                          (fun s0 : Tok =>
                             real_abs
                               (real_mult (real_minus_r (mu s0) (nu s0)) (P s0 s)))
                          states)
                      states)
                  (real_mult (real_of_nat (length states))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                  (real_eq_refl _)
                  (kv_sum_const_list Tok
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps)
                     states))).
    + apply (RealSetoid.real_eq_plus_compat
               (real_list_sum Tok
                  (fun s' : Tok =>
                     real_list_sum Tok
                       (fun s : Tok =>
                          real_abs
                            (real_mult (real_minus_r (mu s) (nu s)) (P s s')))
                       states)
                   states)
               (real_mult (real_of_nat (length states))
                  (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                             eps))
               (real_list_sum Tok
                  (fun x : Tok => real_abs (real_minus_r (mu x) (nu x))) states)
               eps
               (kv_dsum_abs_eq P Hnn HP mu nu)
               (kv_inv_absorb (real_of_nat (length states)) kv_N_pos eps)).
Qed.

(* a − c == (a − b) + (b − c) (the pointwise identity behind the D
   triangle) *)
Lemma kv_minus_split : forall a b c0 : Real,
  real_eq (real_minus_r a c0)
          (real_plus (real_minus_r a b) (real_minus_r b c0)).
Proof.
  intros a b c0. unfold real_minus_r.
  apply real_eq_sym.
  apply (real_eq_trans
           (real_plus (real_plus a (real_opp b)) (real_plus b (real_opp c0)))
           (real_plus a (real_plus (real_opp b) (real_plus b (real_opp c0))))
           (real_plus a (real_opp c0))).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (RealSetoid.real_eq_plus_compat a
             (real_plus (real_opp b) (real_plus b (real_opp c0)))
             a (real_opp c0)
             (real_eq_refl a)
             (real_eq_trans
                (real_plus (real_opp b) (real_plus b (real_opp c0)))
                (real_plus (real_plus (real_opp b) b) (real_opp c0))
                (real_opp c0)
                (real_plus_assoc (real_opp b) b (real_opp c0))
                (real_eq_trans
                   (real_plus (real_plus (real_opp b) b) (real_opp c0))
                   (real_plus real_zero (real_opp c0)) (real_opp c0)
                   (RealSetoid.real_eq_plus_compat (real_plus (real_opp b) b)
                      (real_opp c0) real_zero (real_opp c0)
                      (real_eq_trans (real_plus (real_opp b) b)
                         (real_plus b (real_opp b)) real_zero
                         (real_plus_comm (real_opp b) b) (real_plus_opp b))
                      (real_eq_refl (real_opp c0)))
                   (kv_plus_zero_l (real_opp c0))))).
Qed.

(* |a − b| == |b − a| *)
Lemma kv_abs_minus_flip : forall a b : Real,
  real_eq (real_abs (real_minus_r a b)) (real_abs (real_minus_r b a)).
Proof.
  intros a b.
  apply (real_eq_trans
           (real_abs (real_minus_r a b))
           (real_abs (real_opp (real_minus_r a b)))
           (real_abs (real_minus_r b a))).
  - exact (real_eq_sym (real_abs (real_opp (real_minus_r a b)))
             (real_abs (real_minus_r a b))
             (real_abs_opp (real_minus_r a b))).
  - apply real_abs_eq_compat.
    apply (real_eq_trans
             (real_opp (real_plus a (real_opp b)))
             (real_plus (real_opp a) (real_opp (real_opp b)))
             (real_plus b (real_opp a))).
    + exact (real_opp_plus a (real_opp b)).
    + apply (real_eq_trans
               (real_plus (real_opp a) (real_opp (real_opp b)))
               (real_plus (real_opp a) b)
               (real_plus b (real_opp a))
               (RealSetoid.real_eq_plus_compat (real_opp a)
                  (real_opp (real_opp b)) (real_opp a) b
                  (real_eq_refl (real_opp a)) (real_opp_opp b))
               (real_plus_comm (real_opp a) b)).
Qed.

(* D triangle (the Bishop eps form): D(a,c) <= D(a,b) + D(b,c) + ε *)
Lemma kv_D_triangle : forall (a b cc : Tok -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_le (Ddist a cc)
          (real_plus (Ddist a b) (real_plus (Ddist b cc) eps)).
Proof.
  intros a b cc eps Heps.
  assert (Hshare : real_lt real_zero
            (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps))
    by (apply kv_share_pos; exact Heps).
  unfold Ddist.
  apply (real_le_trans
           (real_list_sum Tok
              (fun x : Tok => real_abs (real_minus_r (a x) (cc x))) states)
           (real_list_sum Tok
              (fun x : Tok =>
                 real_plus
                   (real_plus (real_abs (real_minus_r (a x) (b x)))
                              (real_abs (real_minus_r (b x) (cc x))))
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps))
              states)
           (real_plus
              (real_list_sum Tok
                 (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
              (real_plus
                 (real_list_sum Tok
                    (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                 eps))).
  - apply real_list_sum_le. intro x.
    apply (real_le_trans
             (real_abs (real_minus_r (a x) (cc x)))
             (real_abs
                (real_plus (real_minus_r (a x) (b x))
                           (real_minus_r (b x) (cc x))))
             (real_plus
                (real_plus (real_abs (real_minus_r (a x) (b x)))
                           (real_abs (real_minus_r (b x) (cc x))))
                (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                           eps))).
    + apply inr. apply real_abs_eq_compat.
      exact (kv_minus_split (a x) (b x) (cc x)).
    + exact (real_abs_triangle_le_eps (real_minus_r (a x) (b x))
               (real_minus_r (b x) (cc x))
               (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                          eps)
               Hshare).
  - apply inr.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun x : Tok =>
                   real_plus
                     (real_plus (real_abs (real_minus_r (a x) (b x)))
                                (real_abs (real_minus_r (b x) (cc x))))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                states)
             (real_plus
                (real_list_sum Tok
                   (fun x : Tok =>
                      real_plus
                        (real_abs (real_minus_r (a x) (b x)))
                        (real_abs (real_minus_r (b x) (cc x))))
                   states)
                (real_mult (real_of_nat (length states))
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps)))
             (real_plus
                (real_list_sum Tok
                   (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
                (real_plus
                   (real_list_sum Tok
                      (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                   eps))).
    + apply (real_eq_trans _ _ _
               (real_list_sum_add Tok
                  (fun x : Tok =>
                     real_plus
                       (real_abs (real_minus_r (a x) (b x)))
                       (real_abs (real_minus_r (b x) (cc x))))
                  (fun _ : Tok =>
                     real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                               eps)
                  states)
               (RealSetoid.real_eq_plus_compat
                  (real_list_sum Tok
                     (fun x : Tok =>
                        real_plus
                          (real_abs (real_minus_r (a x) (b x)))
                          (real_abs (real_minus_r (b x) (cc x))))
                     states)
                  (real_list_sum Tok
                     (fun _ : Tok =>
                        real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                  eps)
                     states)
                  (real_list_sum Tok
                     (fun x : Tok =>
                        real_plus
                          (real_abs (real_minus_r (a x) (b x)))
                          (real_abs (real_minus_r (b x) (cc x))))
                     states)
                  (real_mult (real_of_nat (length states))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                  (real_eq_refl _)
                  (kv_sum_const_list Tok
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps) states))).
    + apply (real_eq_trans _ _ _
               (RealSetoid.real_eq_plus_compat
                  (real_list_sum Tok
                     (fun x : Tok =>
                        real_plus
                          (real_abs (real_minus_r (a x) (b x)))
                          (real_abs (real_minus_r (b x) (cc x))))
                     states)
                  (real_mult (real_of_nat (length states))
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                  (real_plus
                     (real_list_sum Tok
                        (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
                     (real_list_sum Tok
                        (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states))
                  eps
                  (real_list_sum_add Tok
                     (fun x : Tok => real_abs (real_minus_r (a x) (b x)))
                     (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                  (kv_inv_absorb (real_of_nat (length states)) kv_N_pos eps))
               (real_eq_sym _ _ (real_plus_assoc
                  (real_list_sum Tok
                     (fun x : Tok => real_abs (real_minus_r (a x) (b x))) states)
                  (real_list_sum Tok
                     (fun x : Tok => real_abs (real_minus_r (b x) (cc x))) states)
                  eps))).
Qed.

(* One-step drift of the row error (the core single-step bound of the
   drift theorem): D(K_ev μ, K μ) <= c + ε (row triangle, exchange, Hrow,
   normalization) *)
(* Weighted double-sum reduction:
   Sum_s' Sum_s |μ(s)·(K_ev−K)(s,s')| == Sum_s μ(s)·tv_row(s) *)
Lemma kv_dsum_row_err : forall mu : Tok -> Real,
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_eq (real_list_sum Tok
             (fun s' : Tok =>
                real_list_sum Tok
                  (fun s : Tok =>
                     real_abs
                       (real_mult (mu s) (real_minus_r (K_ev s s') (K s s'))))
                  states)
              states)
          (real_list_sum Tok
             (fun s : Tok => real_mult (mu s) (tv_row s)) states).
Proof.
  intros mu Hnn.
  apply (real_eq_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (mu s) (real_minus_r (K_ev s s') (K s s'))))
                   states)
              states)
           (real_list_sum Tok
              (fun s : Tok =>
                 real_list_sum Tok
                   (fun s' : Tok =>
                      real_abs
                        (real_mult (mu s) (real_minus_r (K_ev s s') (K s s'))))
                   states)
              states) _).
  - apply kv_swap_list.
  - apply real_list_sum_ext. intro s.
    apply (real_eq_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_abs
                     (real_mult (mu s) (real_minus_r (K_ev s s') (K s s'))))
                states)
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_mult (mu s)
                     (real_abs (real_minus_r (K s s') (K_ev s s'))))
                states)
             (real_mult (mu s) (tv_row s))).
    + apply real_list_sum_ext. intro s'.
      apply (real_eq_trans
               (real_abs
                  (real_mult (mu s) (real_minus_r (K_ev s s') (K s s'))))
               (real_mult (real_abs (mu s))
                          (real_abs (real_minus_r (K_ev s s') (K s s'))))
               (real_mult (mu s)
                          (real_abs (real_minus_r (K s s') (K_ev s s'))))).
      * exact (real_abs_mult_req (mu s)
                 (real_minus_r (K_ev s s') (K s s'))).
      * apply (RealSetoid.real_eq_mult_compat (real_abs (mu s))
                 (real_abs (real_minus_r (K_ev s s') (K s s')))
                 (mu s)
                 (real_abs (real_minus_r (K s s') (K_ev s s')))
                 (kv_abs_nonneg_id (mu s) (Hnn s))
                 (kv_abs_minus_flip (K_ev s s') (K s s'))).
    + apply real_list_sum_linear.
Qed.

(* One-step drift of the row error (the core single-step bound of the
   drift theorem): D(K_ev μ, K μ) <= c + ε (row triangle, exchange, Hrow,
   normalization) *)
Lemma kv_step_drift : forall (mu : Tok -> Real) (eps : Real),
  real_lt real_zero eps ->
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_le (Ddist (lstep K_ev mu) (lstep K mu)) (real_plus c eps).
Proof.
  intros mu eps Heps Hnorm Hnn.
  assert (Hshare : real_lt real_zero
            (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos) eps))
    by (apply kv_share_pos; exact Heps).
  unfold Ddist.
  apply (real_le_trans
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_abs (real_minus_r (lstep K_ev mu s') (lstep K mu s'))) states)
           (real_list_sum Tok
              (fun s' : Tok =>
                 real_plus
                   (real_list_sum Tok
                      (fun s : Tok =>
                         real_abs
                           (real_mult (mu s)
                                      (real_minus_r (K_ev s s') (K s s'))))
                      states)
                   (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                              eps))
              states)
           (real_plus c eps)).
  - apply real_list_sum_le. intro s'.
    apply (real_le_trans
             (real_abs (real_minus_r (lstep K_ev mu s') (lstep K mu s')))
             (real_abs
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_mult (mu s) (real_minus_r (K_ev s s') (K s s'))) states))
             (real_plus
                (real_list_sum Tok
                   (fun s : Tok =>
                      real_abs
                        (real_mult (mu s)
                                   (real_minus_r (K_ev s s') (K s s'))))
                   states)
                (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                           eps))).
    + apply inr. apply real_abs_eq_compat.
      exact (kv_lstep2_minus_pt K_ev K mu s').
    + exact (kv_abs_triangle_list_eps Tok
               (fun s : Tok =>
                  real_mult (mu s) (real_minus_r (K_ev s s') (K s s')))
               states (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                  eps) Hshare).
  - apply (real_le_trans
             (real_list_sum Tok
                (fun s' : Tok =>
                   real_plus
                     (real_list_sum Tok
                        (fun s : Tok =>
                           real_abs
                             (real_mult (mu s)
                                        (real_minus_r (K_ev s s') (K s s'))))
                        states)
                     (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                eps))
                states)
             (real_plus
                (real_list_sum Tok (fun s : Tok => real_mult (mu s) (tv_row s))
                   states)
                eps)
             (real_plus c eps)).
    + apply inr.
      apply (real_eq_trans _ _ _
               (real_list_sum_add Tok
                  (fun s' : Tok =>
                     real_list_sum Tok
                       (fun s : Tok =>
                          real_abs
                            (real_mult (mu s)
                                       (real_minus_r (K_ev s s') (K s s'))))
                       states)
                  (fun _ : Tok =>
                     real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                               eps)
                  states)
               (real_eq_trans _ _ _
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum Tok
                        (fun s' : Tok =>
                           real_list_sum Tok
                             (fun s : Tok =>
                                real_abs
                                  (real_mult (mu s)
                                             (real_minus_r (K_ev s s') (K s s'))))
                             states)
                         states)
                     (real_list_sum Tok
                        (fun _ : Tok =>
                           real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                     eps)
                        states)
                     (real_list_sum Tok
                        (fun s : Tok => real_mult (mu s) (tv_row s)) states)
                     (real_mult (real_of_nat (length states))
                        (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                   eps))
                     (kv_dsum_row_err mu Hnn)
                     (kv_sum_const_list Tok
                        (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                   eps) states))
                  (RealSetoid.real_eq_plus_compat
                     (real_list_sum Tok
                        (fun s : Tok => real_mult (mu s) (tv_row s)) states)
                     (real_mult (real_of_nat (length states))
                        (real_mult (real_inv_pos (real_of_nat (length states)) kv_N_pos)
                                   eps))
                     (real_list_sum Tok
                        (fun s : Tok => real_mult (mu s) (tv_row s)) states)
                     eps
                     (real_eq_refl _)
                     (kv_inv_absorb (real_of_nat (length states)) kv_N_pos eps)))).
    + apply (real_le_trans
               (real_plus
                  (real_list_sum Tok (fun s : Tok => real_mult (mu s) (tv_row s))
                     states)
                  eps)
               (real_plus
                  (real_list_sum Tok (fun s : Tok => real_mult (mu s) c) states)
                  eps)
               (real_plus c eps)).
      * apply real_le_plus_compat.
        -- apply real_list_sum_le. intro s.
           apply (real_le_trans
                    (real_mult (mu s) (tv_row s))
                    (real_mult (tv_row s) (mu s))
                    (real_mult (mu s) c)).
           ** apply inr. apply real_mult_comm.
           ** apply (real_le_trans
                        (real_mult (tv_row s) (mu s))
                        (real_mult c (mu s))
                        (real_mult (mu s) c)).
              ++ exact (real_le_mult_compat_weak (tv_row s) c (mu s)
                          (Hnn s) (Hrow s)).
              ++ apply inr. apply real_mult_comm.
        -- apply real_le_refl.
      * apply inr.
        apply (RealSetoid.real_eq_plus_compat
                 (real_list_sum Tok (fun s : Tok => real_mult (mu s) c) states)
                 eps c eps
                 (real_eq_trans _ _ _
                    (real_list_sum_linear_r Tok c mu states)
                    (real_eq_trans _ _ _
                       (RealSetoid.real_eq_mult_compat c
                          (real_list_sum Tok mu states) c real_one
                          (real_eq_refl c) Hnorm)
                       (real_mult_one c)))
                 (real_eq_refl eps)).
Qed.

(* ---------- Drift theorem: the main bound ---------- *)

(* Telescoping main induction: a_n <= n·c + n·ε0 for every ε0 > 0 (the
   three eps/3 branches close exactly) *)
(* Four-term AC regrouping: (a+b)+(c+d) == (a+c)+(b+d) (a purely
   mechanical assoc/comm chain) *)
Lemma kv_regroup4 : forall a b c0 d : Real,
  real_eq (real_plus (real_plus a b) (real_plus c0 d))
          (real_plus (real_plus a c0) (real_plus b d)).
Proof.
  intros a b c0 d.
  apply (real_eq_trans
           (real_plus (real_plus a b) (real_plus c0 d))
           (real_plus a (real_plus b (real_plus c0 d)))
           (real_plus (real_plus a c0) (real_plus b d))).
  - apply real_eq_sym. apply real_plus_assoc.
  - apply (real_eq_trans
             (real_plus a (real_plus b (real_plus c0 d)))
             (real_plus a (real_plus c0 (real_plus b d)))
             (real_plus (real_plus a c0) (real_plus b d))).
    + apply (RealSetoid.real_eq_plus_compat a
               (real_plus b (real_plus c0 d))
               a
               (real_plus c0 (real_plus b d))
               (real_eq_refl a)
               (real_eq_trans
                  (real_plus b (real_plus c0 d))
                  (real_plus (real_plus b c0) d)
                  (real_plus c0 (real_plus b d))
                  (real_plus_assoc b c0 d)
                  (real_eq_trans
                     (real_plus (real_plus b c0) d)
                     (real_plus (real_plus c0 b) d)
                     (real_plus c0 (real_plus b d))
                     (RealSetoid.real_eq_plus_compat (real_plus b c0) d
                        (real_plus c0 b) d
                        (real_plus_comm b c0) (real_eq_refl d))
                     (real_eq_sym _ _ (real_plus_assoc c0 b d))))).
    + apply (real_plus_assoc a c0 (real_plus b d)).
Qed.


(* Assembly chain for kv_assemble_le: kv_regroup4 first, then an assoc
   transposition, with the endpoint absorbed by H3 — the identity
   (cc+h)+((dd+h)+h) == (cc+dd)+ee follows from h+h+h == ee in four
   association steps *)
Lemma kv_assemble_le : forall cc dd h ee : Real,
  real_eq (real_plus h (real_plus h h)) ee ->
  real_eq (real_plus (real_plus cc h) (real_plus (real_plus dd h) h))
          (real_plus (real_plus cc dd) ee).
Proof.
  intros cc dd h ee H3.
  apply (real_eq_trans
           (real_plus (real_plus cc h) (real_plus (real_plus dd h) h))
           (real_plus (real_plus (real_plus cc dd) h) (real_plus h h))
           (real_plus (real_plus cc dd) ee)).
  - apply (real_eq_trans
             (real_plus (real_plus cc h) (real_plus (real_plus dd h) h))
             (real_plus (real_plus cc (real_plus dd h)) (real_plus h h))
             (real_plus (real_plus (real_plus cc dd) h) (real_plus h h))).
    + exact (kv_regroup4 cc h (real_plus dd h) h).
    + exact (RealSetoid.real_eq_plus_compat
               (real_plus cc (real_plus dd h))
               (real_plus h h)
               (real_plus (real_plus cc dd) h)
               (real_plus h h)
               (real_plus_assoc cc dd h) (real_eq_refl (real_plus h h))).
  - apply (real_eq_trans
             (real_plus (real_plus (real_plus cc dd) h) (real_plus h h))
             (real_plus (real_plus cc dd) (real_plus h (real_plus h h)))
             (real_plus (real_plus cc dd) ee)).
    + exact (real_eq_sym _ _
               (real_plus_assoc (real_plus cc dd) h (real_plus h h))).
    + exact (RealSetoid.real_eq_plus_compat
               (real_plus cc dd) (real_plus h (real_plus h h))
               (real_plus cc dd) ee
               (real_eq_refl (real_plus cc dd)) H3).
Qed.

Lemma kv_drift_P : forall (n : nat) (mu : Tok -> Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  forall eps0 : Real,
  real_lt real_zero eps0 ->
  real_le (Ddist (kev_iter n mu) (k_iter n mu))
          (real_plus (real_mult (real_of_nat n) c)
                     (real_mult (real_of_nat n) eps0)).
Proof.
  intro n. induction n as [| n IH]; intros mu Hnorm Hnn eps0 Heps0.
  - cbn [kev_iter k_iter real_of_nat].
    apply RealSetoid.real_eq_le.
    apply (real_eq_trans (Ddist mu mu) real_zero
             (real_plus (real_mult real_zero c) (real_mult real_zero eps0))).
    + exact (kv_D_zero mu).
    + apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult real_zero c) (real_mult real_zero eps0))
               (real_plus real_zero real_zero) real_zero).
      * apply (RealSetoid.real_eq_plus_compat (real_mult real_zero c)
                 (real_mult real_zero eps0) real_zero real_zero
                 (real_eq_trans _ _ _ (real_mult_comm real_zero c)
                    (real_mult_zero c))
                 (real_eq_trans _ _ _ (real_mult_comm real_zero eps0)
                    (real_mult_zero eps0))).
      * apply real_plus_zero.
  - cbn [kev_iter k_iter real_of_nat].
    assert (HXn : real_eq (real_list_sum Tok (kev_iter n mu) states) real_one)
      by exact (kv_kev_iter_norm n mu Hnorm).
    assert (HZn : real_eq (real_list_sum Tok (k_iter n mu) states) real_one)
      by exact (kv_k_iter_norm n mu Hnorm).
    assert (HXnn : forall s : Tok, real_le real_zero (kev_iter n mu s))
      by exact (kv_kev_iter_nonneg n mu Hnn).
    assert (Ht3 : real_lt real_zero
              (real_mult (real_inv_pos (real_plus (real_plus real_one real_one)
                                          real_one)
                           kv_three_R_pos) eps0)).
    { apply real_mult_pos_compat.
      - apply real_inv_pos_pos.
      - exact Heps0. }
    (* 3·H == ε0 for H = inv3·ε0 (closed exactly by kv_inv_absorb) *)
    assert (H3B : real_eq
              (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))) eps0).
    {{ apply (real_eq_trans
               (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
               (real_plus (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
               eps0).
      - apply real_plus_assoc.
      - apply (real_eq_trans
                 (real_plus (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
                 (real_mult (real_plus (real_plus real_one real_one) real_one) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
                 eps0).
        + apply (kv_plus_self_three (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)).
        + exact (kv_inv_absorb (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos eps0). }}
    (* Main chain: triangle(ε/3) + row error(ε/3) + non-expansiveness(ε/3),
       summing to exactly ε0 *)
    apply (real_le_trans _ _ _ (kv_D_triangle
              (lstep K_ev (kev_iter n mu)) (lstep K (kev_iter n mu))
              (lstep K (k_iter n mu)) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) Ht3)).
    + apply (real_le_trans _
               (real_plus
                  (real_plus c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))
                  (real_plus (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))))
               _).
      * apply real_le_plus_compat.
        -- exact (real_le_trans _ _ _
                     (kv_step_drift (kev_iter n mu) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) Ht3 HXn HXnn)
                     (inr (RealSetoid.real_eq_plus_compat c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)
                             (real_eq_refl c) (real_eq_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))))).
        -- exact (real_le_trans _ _ _
                     (real_le_plus_compat _ _ _ _
                        (kv_nonexpansive K Krow
                           (fun s s'' : Tok =>
                              real_le_from_lt_aux real_zero (K s s'') (Kpos s s''))
                           (kev_iter n mu) (k_iter n mu) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) Ht3)
                        (real_le_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
                     (real_le_trans _ _ _
                        (real_le_plus_compat _ _ _ _
                           (real_le_plus_compat _ _ _ _
                              (IH mu Hnorm Hnn eps0 Heps0)
                              (real_le_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
                           (real_le_refl (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))
                        (inr (real_eq_sym _ _ (real_plus_assoc (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))
                           (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)
                           (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0)))))).

      * apply (real_le_trans _ (real_plus (real_plus c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))) eps0) _).
        -- exact (real_le_trans _ _ _
                     (inr (kv_regroup4 c (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) (real_plus (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0) (real_mult (real_inv_pos (real_plus (real_plus real_one real_one) real_one) kv_three_R_pos) eps0))))
                     (real_le_plus_compat _ _ _ _
                        (real_le_refl (real_plus c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))))
                        (inr H3B))).
        -- apply inr.
           (* Four-term regrouping (assoc, in-group commutation, assoc
             again) followed by the distributive absorption:
             (c+(n·c+n·ε0))+ε0 == (1+n)·c+(1+n)·ε0 *)
           apply (real_eq_trans
                    (real_plus (real_plus c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0))) eps0)
                    (real_plus (real_plus c (real_mult (real_of_nat n) c)) (real_plus eps0 (real_mult (real_of_nat n) eps0)))
                    (real_plus (real_mult (real_plus real_one (real_of_nat n)) c) (real_mult (real_plus real_one (real_of_nat n)) eps0))
                    (real_eq_trans _ _ _
                       (real_eq_sym _ _ (real_plus_assoc c (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) eps0))
                       (real_eq_trans _ _ _
                          (RealSetoid.real_eq_plus_compat c
                             (real_plus (real_plus (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0)) eps0)
                             c
                             (real_plus (real_mult (real_of_nat n) c) (real_plus (real_mult (real_of_nat n) eps0) eps0))
                             (real_eq_refl c)
                             (real_eq_sym _ _ (real_plus_assoc (real_mult (real_of_nat n) c) (real_mult (real_of_nat n) eps0) eps0)))
                          (real_eq_trans _ _ _
                             (RealSetoid.real_eq_plus_compat c
                                (real_plus (real_mult (real_of_nat n) c) (real_plus (real_mult (real_of_nat n) eps0) eps0))
                                c
                                (real_plus (real_mult (real_of_nat n) c) (real_plus eps0 (real_mult (real_of_nat n) eps0)))
                                (real_eq_refl c)
                                (RealSetoid.real_eq_plus_compat (real_mult (real_of_nat n) c)
                                   (real_plus (real_mult (real_of_nat n) eps0) eps0)
                                   (real_mult (real_of_nat n) c)
                                   (real_plus eps0 (real_mult (real_of_nat n) eps0))
                                   (real_eq_refl (real_mult (real_of_nat n) c))
                                   (real_plus_comm (real_mult (real_of_nat n) eps0) eps0)))
                             (real_plus_assoc c (real_mult (real_of_nat n) c) (real_plus eps0 (real_mult (real_of_nat n) eps0))))))
                    (RealSetoid.real_eq_plus_compat
                       (real_plus c (real_mult (real_of_nat n) c)) (real_plus eps0 (real_mult (real_of_nat n) eps0))
                       (real_mult (real_plus real_one (real_of_nat n)) c) (real_mult (real_plus real_one (real_of_nat n)) eps0)
                       (real_eq_trans _ _ _
                          (RealSetoid.real_eq_plus_compat c (real_mult (real_of_nat n) c)
                             (real_mult real_one c) (real_mult (real_of_nat n) c)
                             (real_eq_sym _ _ (kv_one_mult_l c))
                             (real_eq_refl (real_mult (real_of_nat n) c)))
                          (real_eq_sym _ _ (kv_distrib_r real_one (real_of_nat n) c)))
                       (real_eq_trans _ _ _
                          (RealSetoid.real_eq_plus_compat eps0 (real_mult (real_of_nat n) eps0)
                             (real_mult real_one eps0) (real_mult (real_of_nat n) eps0)
                             (real_eq_sym _ _ (kv_one_mult_l eps0))
                             (real_eq_refl (real_mult (real_of_nat n) eps0)))
                          (real_eq_sym _ _ (kv_distrib_r real_one (real_of_nat n) eps0))))).

Qed.

(* ================== Drift main result: the bound (Bishop eps form) =======
   Under the premise Hrow (a uniform row-error constant), the TV drift of
   the two-kernel iteration after n steps is <= n·c + ε. *)
Theorem kv_drift_bound : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  real_le (Ddist (kev_iter n mu) (k_iter n mu))
          (real_plus (real_mult (real_of_nat n) c) eps).
Proof.
  intros n mu eps Hnorm Hnn Heps.
  destruct n as [| m].
  - cbn [kev_iter k_iter real_of_nat].
    (* Base case: the equation 0 == 0·c + eps is not directly available;
       the route is the positive chain D = 0 <= eps == 0·c + eps *)
    apply (real_le_trans _ eps _).
    + apply (real_le_trans _ real_zero _).
      * apply RealSetoid.real_eq_le. exact (kv_D_zero mu).
      * apply real_le_from_lt_aux. exact Heps.
    + apply inr.
      apply real_eq_sym.
      apply (real_eq_trans
               (real_plus (real_mult real_zero c) eps)
               (real_plus real_zero eps)
               eps).
      * exact (RealSetoid.real_eq_plus_compat (real_mult real_zero c) eps
                 real_zero eps
                 (real_eq_trans _ _ _ (real_mult_comm real_zero c)
                    (real_mult_zero c))
                 (real_eq_refl eps)).
      * apply kv_plus_zero_l.
  - assert (Hshare : real_lt real_zero
              (real_mult (real_inv_pos (real_of_nat (Datatypes.S m))
                           (kv_ofnat_S_pos m)) eps))
      by (apply real_mult_pos_compat;
          [apply real_inv_pos_pos | exact Heps]).
    apply (real_le_trans
             (Ddist (kev_iter (Datatypes.S m) mu) (k_iter (Datatypes.S m) mu))
             (real_plus (real_mult (real_of_nat (Datatypes.S m)) c)
                        (real_mult (real_of_nat (Datatypes.S m))
                           (real_mult
                              (real_inv_pos (real_of_nat (Datatypes.S m))
                                           (kv_ofnat_S_pos m)) eps)))
             (real_plus (real_mult (real_of_nat (Datatypes.S m)) c) eps)).
    + exact (kv_drift_P (Datatypes.S m) mu Hnorm Hnn _ Hshare).
    + apply (RealSetoid.real_le_id_r _ _ _
               (RealSetoid.real_eq_plus_compat
                  (real_mult (real_of_nat (Datatypes.S m)) c)
                  (real_mult (real_of_nat (Datatypes.S m))
                     (real_mult (real_inv_pos (real_of_nat (Datatypes.S m))
                                (kv_ofnat_S_pos m)) eps))
                  (real_mult (real_of_nat (Datatypes.S m)) c)
                  eps
                  (real_eq_refl (real_mult (real_of_nat (Datatypes.S m)) c))
                  (kv_inv_absorb (real_of_nat (Datatypes.S m))
                     (kv_ofnat_S_pos m) eps))).
      apply real_le_refl.
Qed.


Theorem kv_drift_bound_tv : forall (n : nat) (mu : Tok -> Real) (eps : Real),
  real_eq (real_list_sum Tok mu states) real_one ->
  (forall s : Tok, real_le real_zero (mu s)) ->
  real_lt real_zero eps ->
  real_le (tvL (kev_iter n mu) (k_iter n mu))
          (real_mult (real_inv_pos (real_plus real_one real_one) kv_two_R_pos)
                     (real_plus (real_mult (real_of_nat n) c) eps)).
Proof.
  intros n mu eps Hnorm Hnn Heps. unfold tvL.
  apply real_le_mult_compat_r.
  - apply real_le_from_lt_aux. apply real_inv_pos_pos.
  - exact (kv_drift_bound n mu eps Hnorm Hnn Heps).
Qed.

End UpKVDrift.

(* Extraction probe note: this file carries no in-file Extraction command.
   Extraction verification runs through the gate7 Separate Extraction driver
   (single-command rule) against the built tree, with the driver's output
   kept out of the tree; the named statements above extract with
   [Obj.magic] = 0 and no erasure under that driver. *)

(* ---------- assumption audit (self-certified, zero acknowledgments):
   live Print Assumptions lines are the audit port -- every compile prints
   the Closed line for each audited statement face. ---------- *)
Print Assumptions Z_keep_pos.
Print Assumptions N_R_pos.
Print Assumptions kev_row_tv_exact.
Print Assumptions kev_row_tv_bound.
Print Assumptions kev_row_tv_one_minus_Z.
Print Assumptions kv_drift_bound.
Print Assumptions kv_drift_bound_tv.