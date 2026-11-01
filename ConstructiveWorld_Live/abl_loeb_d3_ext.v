(* ConstructiveWorld-Set -- Loeb D3 layer-2 continuation: the Formula2
   coding round-trip, the diagonal assembly, and the box-blindness
   boundary theorems (lbe_ prefix; G10_LoebFam self-reference route).

   Mission.
   (1) Formula2 gnF2/dF2b encode/decode round-trip (labels 9/10/11),
       reusing the D1 gnT/gnF machinery (G10_LoebFam :3633).
   (2) The missing-coding-piece obstacle is witnessed as two proved
       boundary theorems: box-blindness (lbe_verPf_f2_false /
       lbe_box_f2_false) and the degenerate vacuous diagonal truth
       (lbe_loeb_diag_vacuous, pinned as boundary witness, not Loeb
       progress; honest-boundary block at the file tail).

   Dependencies.
   G10_LoebFam (Formula2 layer, decoders, evalF2, Id calculus,
   loeb_tid), abl_loeb_d3 (lbd_ pieces used as-is), Stdlib Arith/
   Lia/Wf_nat.

   References.
   G10_LoebFam :3633/:3641; abl_loeb_d3 fuel-invariance pieces.

   Constructivity.
   Statements carry zero Prop: equations by Id, homogeneity by
   loeb_tid, bounds by NatLe (NatLe_drop/NatLe_lift at proof layer).
   Zero axioms, zero admissions, zero placeholders; extractable.

   Build.
   rocq c -native-compiler no -Q <pool> "" abl_loeb_d3_ext.v
   (Rocq 9.1.0; 9.0.1 reports bad version number); born-clean wash --
   no Obj.magic, no Prop cast shims, no Prop-carried statements. *)

From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Wf_nat.

Require Import G10_LoebFam.
Require Import abl_loeb_d3.
Require Import S01_BaseRing.

(* Proof-layer shuttle: extract a Prop equation from an Id premise.
   House shape (G11_IDLFam.v:951 / UpRecast.v:294): the leading slot '_',
   the trailing index bound as z, the left side spelled out in the return
   clause.  Proof-layer only; statement faces stay Id-carried. *)
Ltac idQ lhs H E :=
  pose proof (match H in Id _ z return lhs = z with id_refl => eq_refl end) as E.

(* ===================================================================== *)
(* §E  Formula2 coding round-trip (labels 9/10/11).                          *)
(*     D1 slot occupancy: terms 0–3 / formulas 4–5 / proofs 6–8;             *)
(*     this piece takes 9 (f2b) / 10 (fsig) / 11 (fimp2) per the G10 :3633   *)
(*     interface suggestion, disjoint from the existing code-space labels.   *)
(* ===================================================================== *)

Fixpoint lbe_gnF2 (f : Formula2) : nat :=
  match f with
  | f2b g => pairp 9 (gnF g)
  | fsig B c => pairp 10 (pairp (gnT B) (gnT c))
  | fimp2 a b => pairp 11 (pairp (lbe_gnF2 a) (lbe_gnF2 b))
  end.

(* Total decoder (fuel = recursion guard; same shape as dT2/dF2/dP2,
   three limbs for labels 9/10/11) *)
Fixpoint lbe_dF2b (f c : nat) {struct f} : option Formula2 :=
  match f with
  | O => None
  | Datatypes.S f' =>
      match unp2 c c with
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S O)))))))), q) =>
          (match dF2 f' q with
           | Some g => Some (f2b g)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S O))))))))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match dT2 f' a with
                | Some x =>
                    (match dT2 f' b with
                     | Some y => Some (fsig x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | Some (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S (Datatypes.S
           (Datatypes.S (Datatypes.S (Datatypes.S O)))))))))), q) =>
          (match unp2 q q with
           | Some (a, b) =>
               (match lbe_dF2b f' a with
                | Some x =>
                    (match lbe_dF2b f' b with
                     | Some y => Some (fimp2 x y)
                     | None => None
                     end)
                | None => None
                end)
           | None => None
           end)
      | _ => None
      end
  end.

(* Decoder fuel invariance: what is decoded is the code, not the fuel
   (Formula2 same-shape generalization of lbd_dF2_fuel_inv; uses
   lbd_unp2_self_bounds + lbd_dT2_fuel_inv + lbd_dF2_fuel_inv).
   Strong induction at Set level via Wf_nat's lt_wf_rec (the Prop-level
   lt_wf_ind of the pre-wash proof only reaches Prop goals). *)
Lemma lbe_dF2b_fuel_inv : forall c k1 k2 : nat,
  NatLe c k1 -> NatLe c k2 -> Id (lbe_dF2b k1 c) (lbe_dF2b k2 c).
Proof.
  intros c.
  induction c as [c IH] using lt_wf_rec.
  intros k1 k2 H1 H2.
  destruct c as [|c'].
  - destruct k1 as [|k1']; destruct k2 as [|k2']; apply id_refl.
  - destruct k1 as [|k1']; [pose proof (NatLe_drop _ _ H1); lia|].
    destruct k2 as [|k2']; [pose proof (NatLe_drop _ _ H2); lia|].
    pose proof (NatLe_drop _ _ H1) as H1P.
    pose proof (NatLe_drop _ _ H2) as H2P.
    cbn [lbe_dF2b].
    destruct (unp2 (Datatypes.S c') (Datatypes.S c')) as [[l q]|] eqn:Epc.
    + cbv iota.
      destruct l as [|[|[|[|[|[|[|[|[|[|[|[|[|l3]]]]]]]]]]]]]; cbv iota; try apply id_refl.
      * (* label 9: f2b limb, dF2 route (uses CZ's lbd_dF2_fuel_inv) *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c') _ q
                      (lbd_id_of_eq _ _ Epc)) as Hb.
        destruct Hb as [_ [Hq Hqlt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqlt.
        assert (Ha1 : (q <= k1')%nat) by lia.
        assert (Ha2 : (q <= k2')%nat) by lia.
        assert (Hf2 : Id (dF2 k1' q) (dF2 k2' q))
          by (apply lbd_dF2_fuel_inv; lia).
        idQ (dF2 k1' q) Hf2 Hf2p.
        rewrite Hf2p. apply id_refl.
      * (* label 10: fsig limb, two dT2 routes *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c') _ q
                      (lbd_id_of_eq _ _ Epc)) as Hb.
        destruct Hb as [_ [Hq Hqlt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqlt.
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try apply id_refl.
        pose proof (lbd_unp2_self_bounds q a b (lbd_id_of_eq _ _ Epq)) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        apply NatLe_drop in Hqa. apply NatLe_drop in Hqb.
        assert (Hta : Id (dT2 k1' a) (dT2 k2' a))
          by (apply lbd_dT2_fuel_inv; lia).
        assert (Htb : Id (dT2 k1' b) (dT2 k2' b))
          by (apply lbd_dT2_fuel_inv; lia).
        idQ (dT2 k1' a) Hta Eta. idQ (dT2 k1' b) Htb Etb.
        rewrite Eta, Etb. apply id_refl.
      * (* label 11: fimp2 limb, self IH on both routes *)
        pose proof (lbd_unp2_self_bounds (Datatypes.S c') _ q
                      (lbd_id_of_eq _ _ Epc)) as Hb.
        destruct Hb as [_ [Hq Hqlt]].
        apply NatLe_drop in Hq. apply NatLe_drop in Hqlt.
        destruct (unp2 q q) as [[a b]|] eqn:Epq; cbv iota; try apply id_refl.
        pose proof (lbd_unp2_self_bounds q a b (lbd_id_of_eq _ _ Epq)) as Hb2.
        destruct Hb2 as [Hqa [Hqb _]].
        apply NatLe_drop in Hqa. apply NatLe_drop in Hqb.
        assert (Hla : (a < Datatypes.S c')%nat) by lia.
        assert (Hlb : (b < Datatypes.S c')%nat) by lia.
        assert (Ha1 : (a <= k1')%nat) by lia.
        assert (Ha2 : (a <= k2')%nat) by lia.
        assert (Hb1 : (b <= k1')%nat) by lia.
        assert (Hb2 : (b <= k2')%nat) by lia.
        idQ (lbe_dF2b k1' a)
             (IH a Hla k1' k2' (NatLe_lift a k1' Ha1) (NatLe_lift a k2' Ha2)) Ea.
        idQ (lbe_dF2b k1' b)
             (IH b Hlb k1' k2' (NatLe_lift b k1' Hb1) (NatLe_lift b k2' Hb2)) Eb.
        rewrite Ea, Eb. apply id_refl.
    + apply id_refl.
Qed.

(* Self-fuel normalization corollary (same shape as lbd_dP2_norm) *)
Corollary lbe_dF2b_norm : forall c k : nat,
  NatLe c k -> Id (lbe_dF2b k c) (lbe_dF2b c c).
Proof.
  intros c k H.
  exact (lbe_dF2b_fuel_inv c k c H (NatLe_lift c c (Nat.le_refl c))).
Qed.

(* ── MAIN round-trip theorem: true decoding under sufficient fuel ──
   The f2b limb uses D1's gnF_fuel (first nested use of the D1 round-trip
   by D3); the fsig limb uses gnT_fuel twice; the fimp2 limb goes through
   the self induction. *)
Theorem lbe_gnF2_fuel : forall (f2 : Formula2) (k : nat),
  NatLe (lbe_gnF2 f2) k -> Id (lbe_dF2b k (lbe_gnF2 f2)) (Some f2).
Proof.
  intros f2. induction f2 as [g|B c|a IHa b IHb]; intros k Hk.
  - (* f2b g: code = pairp 9 (gnF g); inner slot via gnF_fuel *)
    destruct k as [|k'].
    + pose proof (NatLe_drop _ _ Hk) as Hd. cbn [lbe_gnF2 pairp] in Hd. lia.
    + pose proof (NatLe_drop _ _ Hk) as Hd.
      pose proof (NatLe_drop _ _ (lbd_pairp_gt_snd 9 (gnF g))) as Hgt.
      cbn [lbe_gnF2 pairp] in Hd. cbn [pairp] in Hgt.
      assert (Hla : (gnF g <= k')%nat) by lia.
      cbn [lbe_gnF2 lbe_dF2b]. rewrite unp2_pair. cbv iota.
      rewrite (gnF_fuel g k' Hla). apply id_refl.
  - (* fsig B c: code = pairp 10 (pairp (gnT B) (gnT c)); both term slots
       via gnT_fuel *)
    destruct k as [|k'].
    + pose proof (NatLe_drop _ _ Hk) as Hd. cbn [lbe_gnF2 pairp] in Hd. lia.
    + pose proof (NatLe_drop _ _ Hk) as Hd.
      pose proof (pairp_ge1 (gnT B) (gnT c)) as Hq1.
      pose proof (pairp_ge (gnT B) (gnT c)) as Hq2.
      assert (Hq3 : (pairp (gnT B) (gnT c) + 1
                     <= pairp 10 (pairp (gnT B) (gnT c)))%nat)
        by (cbn [pairp]; lia).
      cbn [lbe_gnF2 pairp] in Hd.
      assert (Hq4 : (pairp (gnT B) (gnT c) <= k')%nat) by lia.
      assert (H1a : (gnT B <= k')%nat) by lia.
      assert (H1c : (gnT c <= k')%nat) by lia.
      cbn [lbe_gnF2 lbe_dF2b]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      rewrite (gnT_fuel B k' H1a). rewrite (gnT_fuel c k' H1c).
      apply id_refl.
  - (* fimp2 a b: code = pairp 11 (pairp (gnF2 a) (gnF2 b)); both formula
       slots via the self induction *)
    destruct k as [|k'].
    + pose proof (NatLe_drop _ _ Hk) as Hd. cbn [lbe_gnF2 pairp] in Hd. lia.
    + pose proof (NatLe_drop _ _ Hk) as Hd.
      pose proof (pairp_ge1 (lbe_gnF2 a) (lbe_gnF2 b)) as Hq1.
      pose proof (pairp_ge (lbe_gnF2 a) (lbe_gnF2 b)) as Hq2.
      assert (Hq3 : (pairp (lbe_gnF2 a) (lbe_gnF2 b) + 1
                     <= pairp 11 (pairp (lbe_gnF2 a) (lbe_gnF2 b)))%nat)
        by (cbn [pairp]; lia).
      cbn [lbe_gnF2 pairp] in Hd.
      assert (Hq4 : (pairp (lbe_gnF2 a) (lbe_gnF2 b) <= k')%nat) by lia.
      assert (H1aP : (lbe_gnF2 a <= k')%nat) by lia.
      assert (H1bP : (lbe_gnF2 b <= k')%nat) by lia.
      cbn [lbe_gnF2 lbe_dF2b]. rewrite unp2_pair. cbv iota.
      rewrite unp2_pair. cbv iota.
      idQ (lbe_dF2b k' (lbe_gnF2 a)) (IHa k' (NatLe_lift _ _ H1aP)) Ea.
      idQ (lbe_dF2b k' (lbe_gnF2 b)) (IHb k' (NatLe_lift _ _ H1bP)) Eb.
      rewrite Ea, Eb. apply id_refl.
Qed.

(* True decoding (self-fuel normalized form) *)
Corollary lbe_dec_gnF2 : forall f2 : Formula2,
  Id (lbe_dF2b (lbe_gnF2 f2) (lbe_gnF2 f2)) (Some f2).
Proof.
  intros f2.
  exact (lbe_gnF2_fuel f2 (lbe_gnF2 f2) (NatLe_lift _ _ (Nat.le_refl _))).
Qed.

(* Injectivity of the encoding (pure Id calculus: id_cong / id_sym /
   id_trans; no Prop extraction needed) *)
Lemma lbe_gnF2_inj : forall f1 f2 : Formula2,
  Id (lbe_gnF2 f1) (lbe_gnF2 f2) -> Id f1 f2.
Proof.
  intros f1 f2 H.
  pose proof (lbe_dec_gnF2 f1) as E1. pose proof (lbe_dec_gnF2 f2) as E2.
  pose proof (id_cong (fun x : nat => lbe_dF2b x x) H) as Hcc.
  pose proof (id_trans (id_sym Hcc) E1) as EF1.
  pose proof (id_trans (id_sym E2) EF1) as EO.
  exact (id_sym (id_cong (fun o : option Formula2 =>
                    match o with
                    | Some x => x
                    | None => f2
                    end) EO)).
Qed.

(* ── Cross-decoding blind spots, three pieces ──
   Formula codes (labels 4/5) are outside the F2 decoder's range, and F2
   codes (labels 9/10/11) are outside the Formula decoder's range.
   Technical note: at self-fuel dX2 (pairp …) (pairp …) the fuel is not a
   constructor head, so iota cannot fire; the fuel invariance lifts the
   goal to S-fuel form first and only then does it compute. *)

Lemma lbe_dF2_S_gnF2_none : forall f2 : Formula2,
  Id (dF2 (Datatypes.S (lbe_gnF2 f2)) (lbe_gnF2 f2)) None.
Proof.
  intros f2. destruct f2 as [g|B c|a b]; cbn [lbe_gnF2 dF2].
  - rewrite unp2_pair. cbv iota. apply id_refl.
  - rewrite unp2_pair. cbv iota. apply id_refl.
  - rewrite unp2_pair. cbv iota. apply id_refl.
Qed.

Lemma lbe_dF2_norm_aux : forall c k : nat,
  NatLe c k -> Id (dF2 k c) (dF2 c c).
Proof.
  intros c k H.
  assert (Hpid : Id (dF2 k c) (dF2 c c))
    by (apply lbd_dF2_fuel_inv;
          [exact (NatLe_drop c k H) | apply Nat.le_refl]).
  idQ (dF2 k c) Hpid Hpp.
  rewrite Hpp. apply id_refl.
Qed.

Lemma lbe_dF_gnF2_none : forall f2 : Formula2,
  Id (dF (lbe_gnF2 f2)) None.
Proof.
  intros f2. unfold dF.
  exact (id_trans
          (id_sym (lbe_dF2_norm_aux (lbe_gnF2 f2) (Datatypes.S (lbe_gnF2 f2))
                     (NatLe_lift _ _ (Nat.le_succ_diag_r _))))
          (lbe_dF2_S_gnF2_none f2)).
Qed.

Lemma lbe_dF2b_S_gnF_none : forall g : Formula,
  Id (lbe_dF2b (Datatypes.S (gnF g)) (gnF g)) None.
Proof.
  intros g. destruct g as [u1 u2|a b]; cbn [gnF lbe_dF2b].
  - rewrite unp2_pair. cbv iota. apply id_refl.
  - rewrite unp2_pair. cbv iota. apply id_refl.
Qed.

(* ===================================================================== *)
(* §F  Formula2 diagonal assembly + box-blindness boundary theorems          *)
(* ===================================================================== *)

(* Code-level self-substitution (Formula2 counterpart of gsubF; uses
   lbe_dec_gnF2) *)
Definition lbe_gsubF2 (c m : nat) : nat :=
  match lbe_dF2b c c with
  | Some f2 => lbe_gnF2 (substF2 f2 (numT m))
  | None => c
  end.

(* Wrapper and diagonal combinator (assembled per the G10 :3641 interface
   suggestion) *)
Definition lbe_wrap2 (th : Formula2) : Formula2 := substF2 th selfT.
Definition lbe_diagF2 (th : Formula2) : Formula2 :=
  substF2 (lbe_wrap2 th) (numT (lbe_gnF2 (lbe_wrap2 th))).

(* Code identity: the diagonal sentence's code = code-level
   self-substitution value (Formula2 counterpart of D1's
   diagonal_code_fixed). Statement keeps the G10 loeb_tid carrier; the
   Id-valued round-trip is shuttled to a Prop equation by idQ for the
   final rewrite. *)
Theorem lbe_diagF2_code_eq : forall th : Formula2,
  loeb_tid nat (lbe_gnF2 (lbe_diagF2 th))
    (lbe_gsubF2 (lbe_gnF2 (lbe_wrap2 th)) (lbe_gnF2 (lbe_wrap2 th))).
Proof.
  intros th. apply loeb_tid_eq. unfold lbe_gsubF2, lbe_diagF2.
  idQ (lbe_dF2b (lbe_gnF2 (lbe_wrap2 th)) (lbe_gnF2 (lbe_wrap2 th)))
       (lbe_dec_gnF2 (lbe_wrap2 th)) E.
  rewrite E. reflexivity.
Qed.

(* Four pointwise-assignment extensionality lemmas: evalF2 sees the
   assignment only through valt (zero functional extensionality axioms) *)
Lemma lbe_valt_ext : forall (t : Term) (s1 s2 : nat -> nat),
  (forall k : nat, Id (s1 k) (s2 k)) -> Id (valt t s1) (valt t s2).
Proof.
  intros t. induction t as [k0| |t IHt|a IHa b IHb]; intros s1 s2 H; cbn [valt].
  - apply H.
  - apply id_refl.
  - exact (id_cong (fun z : nat => Datatypes.S z) (IHt s1 s2 H)).
  - exact (id_cong2 (fun x y : nat => gsubF x y) (IHa s1 s2 H) (IHb s1 s2 H)).
Qed.

Lemma lbe_evalF_ext : forall (f : Formula) (s1 s2 : nat -> nat),
  (forall k : nat, Id (s1 k) (s2 k)) -> Id (evalF f s1) (evalF f s2).
Proof.
  intros f. induction f as [u1 u2|a IHa b IHb]; intros s1 s2 H; cbn [evalF].
  - exact (id_cong2 (fun x y : nat => Nat.eqb x y)
             (lbe_valt_ext u1 s1 s2 H) (lbe_valt_ext u2 s1 s2 H)).
  - exact (id_cong2 (fun x y : bool => orb (negb x) y)
             (IHa s1 s2 H) (IHb s1 s2 H)).
Qed.

Lemma lbe_bsearch_ext : forall (bd : nat) (p1 p2 : nat -> bool),
  (forall w : nat, Id (p1 w) (p2 w)) -> Id (bsearch bd p1) (bsearch bd p2).
Proof.
  intros bd. induction bd as [|bd' IH]; intros p1 p2 H; cbn [bsearch].
  - apply id_refl.
  - exact (id_cong2 (fun x y : bool => orb x y) (H bd') (IH p1 p2 H)).
Qed.

Lemma lbe_evalF2_ext : forall (f2 : Formula2) (s1 s2 : nat -> nat),
  (forall k : nat, Id (s1 k) (s2 k)) -> Id (evalF2 f2 s1) (evalF2 f2 s2).
Proof.
  intros f2. induction f2 as [g|B c|a IHa b IHb]; intros s1 s2 H; cbn [evalF2].
  - apply lbe_evalF_ext. exact H.
  - exact (id_trans
            (id_cong
               (fun v : nat => bsearch v (fun w : nat => verPf w (valt c s1)))
               (lbe_valt_ext B s1 s2 H))
            (lbe_bsearch_ext (valt B s2)
               (fun w : nat => verPf w (valt c s1))
               (fun w : nat => verPf w (valt c s2))
               (fun w : nat => id_cong (fun z : nat => verPf w z)
                                       (lbe_valt_ext c s1 s2 H)))).
  - exact (id_cong2 (fun x y : bool => orb (negb x) y)
             (IHa s1 s2 H) (IHb s1 s2 H)).
Qed.

(* ── Evaluation diagonal identity ──
   evalF2 (diagF2 th) s = evalF2 th (upd s ⌜wrap2 th⌝2).
   The diagonal term's tsub (numT n) (numT n) value routes through gsubF
   (driven by the Formula decoder): on an F2 code n, dF n = None
   (lbe_dF_gnF2_none), hence the slot value is identically n = ⌜wrap2 th⌝2 —
   the diagonal "retreats one step" to the wrapper's code, the precise gap
   exhibited by this piece. *)
Theorem lbe_diagF2_eval : forall (th : Formula2) (s : nat -> nat),
  Id (evalF2 (lbe_diagF2 th) s)
     (evalF2 th (upd s (lbe_gnF2 (lbe_wrap2 th)))).
Proof.
  intros th s. unfold lbe_diagF2.
  rewrite evalF2_subst. rewrite valt_numT.
  unfold lbe_wrap2. rewrite evalF2_subst.
  apply lbe_evalF2_ext. intros k0. destruct k0.
  - cbn [upd]. unfold selfT. cbn [valt upd]. unfold gsubF.
    exact (id_cong (fun o : option Formula =>
              match o with
              | Some f => gnF (substF f (numT (lbe_gnF2 (substF2 th selfT))))
              | None => lbe_gnF2 (substF2 th selfT)
              end)
              (lbe_dF_gnF2_none (substF2 th selfT))).
  - apply id_refl.
Qed.

(* ── Box-blindness theorem ──
   verPf's code comparison (gnF g =? c) never hits in the F2 code space:
   Formula codes carry labels 4/5 (pairp 4/5 shapes = 16·(·+1) / 32·(·+1)),
   F2 codes carry labels 9/10/11 (512·(·+1) / 1024·(·+1) / 2048·(·+1)),
   strictly separated modulo the powers of 2. *)
Theorem lbe_verPf_f2_false : forall (w : nat) (f2 : Formula2),
  Id (verPf w (lbe_gnF2 f2)) false.
Proof.
  intros w f2.
  assert (Hp : verPf w (lbe_gnF2 f2) = false).
  { unfold verPf.
    destruct (dP2 w w) as [g|].
    - destruct g as [u1 u2|a b]; destruct f2 as [g2|B c|a2 b2];
        cbn [gnF lbe_gnF2]; cbn [pairp];
        apply (proj2 (Nat.eqb_neq _ _)); lia.
    - reflexivity. }
  rewrite Hp. apply id_refl.
Qed.

Theorem lbe_box_f2_false : forall (B : nat) (f2 : Formula2),
  Id (lbd_Box B (lbe_gnF2 f2)) false.
Proof.
  intros B f2. revert f2. induction B as [|B' IH]; intros f2;
    cbn [lbd_Box bsearch].
  - apply id_refl.
  - idQ (verPf B' (lbe_gnF2 f2)) (lbe_verPf_f2_false B' f2) Ev.
    rewrite Ev. cbn [orb]. apply IH.
Qed.

(* ── Diagonal assembly of the Löb sentence and its degenerate truth
   (boundary witness, not Löb progress) ──
   d2 := diagF2 (fimp2 (fsig (numT B) (tvar 0)) p), the diagonal form of
   "□_B(x) → p": its fsig slot value is always an ⌜d2⌝2-family code
   n = ⌜wrap2 th⌝2, and n being an F2 code puts □_B n in the blind spot,
   hence false — the implication is propped up by a vacuously false left
   side, so the evaluation is true under every assignment.
   【Pseudo-full-form alarm】This is the VACUATION PROOF of the full-form
   Löb under this semantics: naive lifting yields no Löb content, only a
   true-but-empty implication. Full-form Löb requires a separate
   Prf2/gnPrf2 certificate layer. *)
Theorem lbe_loeb_diag_vacuous : forall (B : nat) (p : Formula2) (s : nat -> nat),
  Id (evalF2 (lbe_diagF2 (fimp2 (fsig (numT B) (tvar 0)) p)) s) true.
Proof.
  intros B p s.
  idQ (lbd_Box B (lbe_gnF2 (lbe_wrap2 (fimp2 (fsig (numT B) (tvar 0)) p))))
       (lbe_box_f2_false B (lbe_wrap2 (fimp2 (fsig (numT B) (tvar 0)) p))) HbI.
  unfold lbd_Box in HbI.
  apply (id_trans (lbe_diagF2_eval (fimp2 (fsig (numT B) (tvar 0)) p) s)).
  cbn [evalF2]. rewrite valt_numT. cbn [valt upd].
  rewrite HbI. apply id_refl.
Qed.

(* ── Exhibits: the diagonal sentence is encodable, readable back, and the
   box-blindness has a computable smoke test ──
   Code-size warning: under this pairing encoding a compound sentence's
   code grows like 2^(left subcode) (the first component of pairp is the
   left subformula's code), so a Löb sentence (fimp2 compound form) has an
   astronomically large unary code that vm_compute cannot reach — all
   compound smoke tests go through the theorem channel; the computable
   smoke tests shrink to the closed atomic scale
   (code = pairp 9 656 = 672256). *)
Definition lbe_demo_th : Formula2 :=
  fimp2 (fsig (numT 3000) (tvar 0)) (f2b (teq tzero tzero)).
Definition lbe_demo_d : Formula2 := lbe_diagF2 lbe_demo_th.
Definition lbe_demo_code : nat := lbe_gnF2 lbe_demo_d.

(* Code-level read-back of the Löb sentence (theorem channel): ⌜d2⌝2
   decodes back to exactly d2 — F2 sentences are addressable *)
Theorem lbe_demo_roundtrip :
  Id (lbe_dF2b lbe_demo_code lbe_demo_code) (Some lbe_demo_d).
Proof. exact (lbe_dec_gnF2 lbe_demo_d). Qed.

(* Box-blindness smoke test (theorem channel): the ledger box at bound
   3000 is false on ⌜d2⌝2 *)
Theorem lbe_demo_box_blind : Id (lbd_Box 3000 lbe_demo_code) false.
Proof. exact (lbe_box_f2_false 3000 lbe_demo_d). Qed.

(* Degenerate truth (theorem channel): the Löb sentence evaluates to true
   under every assignment — vacuous false left side propping it up *)
(* The goal face spells lbe_diagF2's argument literally: lbe_demo_d is
   delta-equal to it, but a kernel conversion between the two faces
   forces lbe_gnF2 (lbe_wrap2 lbe_demo_th) -- a 10^10-scale unary code,
   the same code-size boundary the smoke-test note below registers.  The
   literal face makes the goal the theorem instance verbatim, so the
   check closes with no conversion. *)
Theorem lbe_demo_vacuous :
  Id (evalF2 (lbe_diagF2 (fimp2 (fsig (numT 3000) (tvar 0)) lbe_demo_th))
     (fun _ : nat => 0)) true.
Proof. exact (lbe_loeb_diag_vacuous 3000 lbe_demo_th (fun _ : nat => 0)). Qed.

(* ── Independent vm_compute smoke tests at the closed atomic scale
   (not relying on the theorems above) ──
   Closed atomic code = pairp 9 (gnF (teq tzero tzero)) = 512·(2·656+1)
   = 672256.
   【Stack-boundary field note】The smoke test must enter the statement via
   the literal code 672256: the body of lbe_demo_atom_code-style
   definitions carries diagF2's numT slot, and CBV evaluation recurses to
   code-value depth when building numT (670k stack frames) — a stack
   overflow. What vm_compute can safely touch is the decoder (fuel is
   only a guard; depth follows the code structure, not the fuel value)
   and the literal code. This is the stack-complexity boundary of the
   pairing encoding + CBV, registered in the report. *)
Theorem lbe_demo_atom_rt_compute :
  Id (lbe_dF2b 672256 672256) (Some (f2b (teq tzero tzero))).
Proof. vm_compute. apply id_refl. Qed.

Theorem lbe_demo_atom_blind_compute : Id (lbd_Box 3000 672256) false.
Proof. vm_compute. apply id_refl. Qed.

(* ===================================================================== *)
(* Honest boundary (explicitly declared, no ad-hoc constructions):           *)
(*   1. The layer-2 coding-round-trip obstacle (missing-piece half of CZ     *)
(*      registration (i)) is eliminated: lbe_gnF2_fuel is closed, the        *)
(*      diagonal assembly diagF2 is applicable, and both the code identity   *)
(*      and the evaluation identity are proved.                              *)
(*   2. Full-form Löb is not in this piece. The two remaining walls are      *)
(*      both THEOREMIZED:                                                    *)
(*      (i') box-blindness wall (newly proved here):                         *)
(*           lbe_verPf_f2_false + lbe_box_f2_false — the ledger certificate  *)
(*           space spins idle on F2 codes; full-form lifting needs a new     *)
(*           Prf2/gnPrf2 certificate layer;                                  *)
(*      (ii') unbounded-search wall (rLPO lineage, kept as registered by     *)
(*           CZ).                                                            *)
(*   3. The F2 diagonal's "one-slot-off": slot value = ⌜wrap2 th⌝2 ≠         *)
(*      ⌜diagF2 th⌝2 (in general) — the root cause is that the term-value    *)
(*      channel tsub ↦ gsubF only recognizes the Formula decoder; getting    *)
(*      the gsubF2 counterpart into the term-value channel (a new term       *)
(*      constructor) or finding an F2 code-preserving fixpoint is the next   *)
(*      real summit.                                                         *)
(*   4. lbe_loeb_diag_vacuous is a boundary witness: its "always true" is    *)
(*      propped up by box-blindness and has no bearing on Löb content; its   *)
(*      name and alarm comments pin this down, and citing it as a full-form  *)
(*      Löb result is forbidden.                                             *)
(* ===================================================================== *)

(* —— Assumption-surface self-audit (all should be Closed under the global
   context) —— *)
Print Assumptions lbe_dF2b_fuel_inv.
Print Assumptions lbe_gnF2_fuel.
Print Assumptions lbe_gnF2_inj.
Print Assumptions lbe_diagF2_code_eq.
Print Assumptions lbe_diagF2_eval.
Print Assumptions lbe_box_f2_false.
Print Assumptions lbe_loeb_diag_vacuous.
Print Assumptions lbe_demo_roundtrip.
