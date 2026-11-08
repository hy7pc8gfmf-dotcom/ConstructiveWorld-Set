(* ConstructiveWorld-Set -- minimal-instance discharge file for the G13 eviction family. *)

(** * G13 eviction discharge: six slots discharged on minimal instance worlds.

    Mission.  Discharges six slot obligations of the G13 eviction family on
      two minimal instance worlds: the one-point SumOver instance
      [uab_ssUnit]/[uab_soUnit] at the [Id] layer (positivity, evicted
      partition, row normalization, detailed balance), and the two-point
      carrier [bool] with [uab_t2sum]/[uab_half] at the req layer.

    Dependencies.  Requires [S01_BaseRing], [S02_CauchyComplete],
      [S03_QExp], [S04_RealExpLogConv], [S05_AlignmentGRPO],
      [S06_DiffSamplingGibbs], [S07_RealSetoidExpLog], [S08_RealMainlineDPO],
      [S09_EntropyReal], [S10_KVQuantTrig], [S11_TP3B5], [S12_B5RecycleSF],
      [S13_NLiveAudit], [S14_B5BatchBlock], [S15_TailFEPUp],
      [G13_EvictFam] of this development.

    References.  This development, the same-named baseline module in
      ConstructiveWorld-Main; statement names verbatim (statements
      byte-frozen; binder shells carrier-ized to [Real] per tree precedent).

    Constructivity.  All named statements and fields are carried by [Set]
      (decidable Q-carriers and boolean identity carriers); [coqchk]
      reports [Axioms: none].  Concrete-carrier statement faces extract
      with [Obj.magic] = 0 and no erasure; the abstract-interface instance
      world ([uab_ssUnit]/[uab_ssUnit_elem] at a quantified [RealInterface])
      carries the carrier casts inherent to that quantifier face.

    Build.  [coqc -native-compiler no -q -Q . "" <module>.v] compiles cleanly
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
Require Import G13_EvictFam.
Require Import S01_BaseRing.

(* ======== part one, the Id layer: the one-point SumOver bundle
  (the minimal SumOver instance world) ======== *)

Lemma uab_unit_unique : forall a b : unit, Id a b.
Proof.
  intros a b.
  destruct a, b.
  reflexivity.
Qed.

Definition uab_ssUnit {RI : RealInterface} : StateSpace RI :=
  {| S := unit;
     szero := tt;
     splus := fun _ _ => tt;
     smult := fun _ _ => tt;
     sopp := fun _ => tt;
     splus_assoc := fun _ _ _ => id_refl;
     splus_comm := fun _ _ => id_refl;
     splus_zero := fun a => uab_unit_unique tt a;
     splus_opp := fun _ => id_refl;
     smult_one := fun a => uab_unit_unique tt a;
     smult_assoc := fun _ _ _ => id_refl;
     smult_distrib_r := fun _ _ _ => id_refl;
     smult_distrib_l := fun _ _ _ => id_refl;
     smetric := fun _ _ => zero;
     smetric_sym := fun _ _ => id_refl;
     smetric_pos := fun _ _ => le_refl zero;
     smetric_zero := fun a b _ => uab_unit_unique a b;
     smetric_triangle :=
       fun _ _ _ => le_id_r zero zero (plus zero zero) (id_sym (plus_zero zero)) (le_refl zero);
     clim := fun _ _ => unit;
     clim_unique := fun _ l1 l2 _ _ => uab_unit_unique l1 l2;
     cauchy_complete_S := fun _ _ => existT (fun _ : unit => unit) tt tt |}.

Lemma uab_ssUnit_elem {RI : RealInterface} : @S RI uab_ssUnit.
Proof.
  unfold uab_ssUnit.
  exact tt.
Defined.

Definition uab_soUnit {RI : RealInterface} : SumOver RI (@uab_ssUnit RI) :=
  {| sum_over_S := fun f => f uab_ssUnit_elem;
     sum_over_S_linear := fun a f => (@id_refl _ (mult a (f uab_ssUnit_elem)));
     sum_over_S_add := fun f g => (@id_refl _ (plus (f uab_ssUnit_elem) (g uab_ssUnit_elem)));
     sum_over_S_ext := fun f g H => H uab_ssUnit_elem;
     sum_over_S_le := fun f g H => H uab_ssUnit_elem;
     sum_over_S_nonneg := fun f H => H uab_ssUnit_elem;
     sum_over_S_zero_nonneg := fun f _ H0 s =>
       (match s as x return (Id (f x) zero) with
        | tt => H0
        end);
     abs_sum_le := fun f => le_refl (abs (f uab_ssUnit_elem)) |}.

(* ---- swap-family core lemma (Id layer, arbitrary carrier):
        p(s) * (p(s') * c) == p(s') * (p(s) * c) ---- *)
Lemma uabT13c_swap_id_gen :
  forall (A : Set) {RI : RealInterface} (p : A -> @R RI) (c : @R RI) (s s' : A),
    Id (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros A RI p c s s'.
  (* named witness assembly: the left-associativity witness, then the
  commutation witness, then the right-associativity inverse witness;
  all three steps are named *)
  pose proof (mult_assoc (p s) (p s') c) as Hassoc_l.
  pose proof (id_cong (fun x : @R RI => mult x c) (mult_comm (p s) (p s')))
    as Hcomm.
  pose proof (id_sym (mult_assoc (p s') (p s) c)) as Hassoc_r.
  exact (id_trans Hassoc_l (id_trans Hcomm Hassoc_r)).
Qed.

(* ---- slot 1 from G13:61 (partition positivity discharged: the
        one-point sum is the single factor row, [exp_neg_pos]
        substituted directly) ---- *)
Theorem uabT13c_evict61 :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : lt zero D) (energy : @S RI uab_ssUnit -> @R RI),
    lt zero (@evict_Z_thermo RI uab_ssUnit uab_soUnit D D_pos energy).
Proof.
  intros RI D D_pos energy.
  unfold evict_Z_thermo, evict_boltzmann_factor, sum_over_S.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy uab_ssUnit_elem))).
Qed.

(* ---- slot 4 from G13:87 (evicted-partition positivity: the keep-all
        decision supplies the branch, reducing to slot 1 after iota)
        ---- *)
Theorem uabT13c_evict87 :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : lt zero D) (energy : @S RI uab_ssUnit -> @R RI),
    lt zero (@evict_evicted_partition RI uab_ssUnit uab_soUnit D D_pos energy
               (fun _ : @S RI uab_ssUnit => unit)
               (fun _ : @S RI uab_ssUnit => inl tt : Or unit (Not unit))).
Proof.
  intros RI D D_pos energy.
  unfold evict_evicted_partition, evict_boltzmann_factor, sum_over_S.
  exact (exp_neg_pos (mult (inv_pos D D_pos) (energy uab_ssUnit_elem))).
Qed.

(* ---- slot 2 from G13:68 (row normalization discharged: the
        constant-one kernel, the one-point sum of a row is the row
        itself, hence one) ---- *)
Theorem uabT13c_evict68 :
  forall {RI : RealInterfaceEnhanced} (s : @S RI uab_ssUnit),
    Id (@sum_over_S RI uab_ssUnit uab_soUnit (fun s' : @S RI uab_ssUnit => one)) one.
Proof.
  intros RI s.
  exact id_refl.
Qed.

(* ---- slot 3 from G13:71 (detailed balance discharged for the
        source-kernel scaling family t(s,s') = dist(s') * c;
        partition positivity is discharged by slot 1, with no data
        slots; the one-point world is the minimal instance face)
        ---- *)
Theorem uabT13c_evict71 :
  forall {RI : RealInterfaceEnhanced}
         (D : @R RI) (D_pos : lt zero D) (energy : @S RI uab_ssUnit -> @R RI) (c : @R RI),
    forall s s' : @S RI uab_ssUnit,
      Id (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                  (uabT13c_evict61 D D_pos energy) s)
               (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                        (uabT13c_evict61 D D_pos energy) s') c))
         (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                  (uabT13c_evict61 D D_pos energy) s')
               (mult (@evict_boltzmann_dist_attn RI uab_ssUnit uab_soUnit D D_pos energy
                        (uabT13c_evict61 D D_pos energy) s) c)).
Proof.
  intros RI D D_pos energy c s s'.
  (* controlled unfolding at the definition level: dist_attn unfolds to
  the raw scaled-product family, the swap lemma is instantiated on the
  bare products (named witnesses), and the unfolded face closes by
  conversion *)
  unfold evict_boltzmann_dist_attn.
  pose proof (uabT13c_swap_id_gen (@S RI uab_ssUnit)
                (fun x : @S RI uab_ssUnit =>
                   mult (@inv_pos RI
                           (@evict_Z_thermo RI uab_ssUnit uab_soUnit D D_pos energy)
                           (uabT13c_evict61 D D_pos energy))
                        (@evict_boltzmann_factor RI uab_ssUnit D D_pos energy
                           x))
                c s s') as Hswap.
  exact Hswap.
Qed.

(* ======== part two, the req layer: the two-point supply world
  (concrete [Real] carrier, no bridges, no data slots) ======== *)
Import RealInterfaceEnhancedMod.
Require Import G13_EvictFam.

Section UabT13cG13Req.

Definition uab_t2sum (f : bool -> Real) : Real := plus (f true) (f false).

Definition uab_half : Real :=
  inv_pos (plus one one) (plus_positive one one one_pos one_pos).

(* ---- swap-family core lemma (req layer, two-point carrier) ---- *)
Lemma uabT13c_swap_req_gen :
  forall (p : bool -> Real) (c : Real) (s s' : bool),
    req (mult (p s) (mult (p s') c)) (mult (p s') (mult (p s) c)).
Proof.
  intros p c s s'.
  (* named witness assembly: left associativity, then the commutation
  compatibility step (comm and refl as its two premises), then the
  right associativity inverse, with the middle terms of req_trans
  explicit *)
  pose proof (mult_assoc (p s) (p s') c) as Hassoc_l.
  pose proof (req_mult_compat (mult (p s) (p s')) (mult (p s') (p s)) c c
                (mult_comm (p s) (p s')) (req_refl c)) as Hcomm.
  pose proof (req_sym (mult (p s') (mult (p s) c))
                      (mult (mult (p s') (p s)) c)
                      (mult_assoc (p s') (p s) c)) as Hassoc_r.
  exact (req_trans (mult (p s) (mult (p s') c))
                   (mult (mult (p s) (p s')) c)
                   (mult (p s') (mult (p s) c))
                   Hassoc_l
                   (req_trans (mult (mult (p s) (p s')) c)
                              (mult (mult (p s') (p s)) c)
                              (mult (p s') (mult (p s) c))
                              Hcomm
                              Hassoc_r)).
Qed.

(* the two-point row-normalization algebraic core: half + half == one *)
Lemma uabT13c_half_row : req (plus uab_half uab_half) one.
Proof.
  unfold uab_half.
  assert (H1 : req (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                   (inv_pos (plus one one) (plus_positive one one one_pos one_pos))).
  { exact (req_trans (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos))
                     (mult_comm one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult_one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))). }
  assert (HDL : req (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                    (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                          (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))).
  { exact (req_trans (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                     (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                     (mult_comm (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                     (req_trans (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (plus one one))
                                (plus (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one))
                                (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                                (distrib (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one one)
                                (req_plus_compat (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                                                 (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one) (mult_comm (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) one)))). }
  (* named witness assembly: right unit-multiplication normalization
  twice, then positive-sum compatibility, then distributivity over the
  inverse, closing with the inverse-correctness identity; all four
  witnesses are named and the middle terms are explicit *)
  pose proof (req_sym (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) H1) as Hone_r.
  pose proof (req_plus_compat (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                Hone_r Hone_r) as Hsum.
  pose proof (req_sym (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
                      (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
                      HDL) as Hdistr.
  pose proof (inv_pos_correct (plus one one) (plus_positive one one one_pos one_pos))
    as Hinv.
  exact (req_trans
           (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
           (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
           one
           (req_trans
              (plus (inv_pos (plus one one) (plus_positive one one one_pos one_pos)) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
              (plus (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))) (mult one (inv_pos (plus one one) (plus_positive one one one_pos one_pos))))
              (mult (plus one one) (inv_pos (plus one one) (plus_positive one one one_pos one_pos)))
              Hsum
              Hdistr)
           Hinv).
Qed.

(* ---- slot 5 from G13:464 (row normalization discharged: the
        two-point uniform kernel, row sum = half + half = one)
        ---- *)
Theorem uabT13c_evq_norm464 :
  forall s : bool,
    req (uab_t2sum (fun s' : bool => uab_half)) one.
Proof.
  intro s.
  unfold uab_t2sum.
  exact uabT13c_half_row.
Qed.

(* ---- two-point partition positivity (supplies Z_thermo_pos for
        slot 6: pointwise exp_neg_pos plus the two-point positive sum)
        -- *)
Theorem uabT13c_evq_Zpos2 :
  forall (D : Real) (D_pos : lt zero D) (energy : bool -> Real),
    lt zero (@evq_Z_thermo bool uab_t2sum D D_pos energy).
Proof.
  intros D D_pos energy.
  unfold evq_Z_thermo, uab_t2sum, evq_boltzmann_factor.
  exact (plus_positive (exp_neg (mult (inv_pos D D_pos) (energy true)))
                       (exp_neg (mult (inv_pos D D_pos) (energy false)))
                       (exp_neg_pos (mult (inv_pos D D_pos) (energy true)))
                       (exp_neg_pos (mult (inv_pos D D_pos) (energy false)))).
Qed.

(* ---- slot 6 from G13:468 (detailed balance discharged for the
        source-kernel scaling family t(s,s') = dist(s') * c; the
        two-point positive sum discharges partition positivity, with
        no data slots) ---- *)
Theorem uabT13c_evq_db468 :
  forall (D : Real) (D_pos : lt zero D) (energy : bool -> Real) (c : Real),
    forall s s' : bool,
      req (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                   (uabT13c_evq_Zpos2 D D_pos energy) s)
                (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                         (uabT13c_evq_Zpos2 D D_pos energy) s') c))
          (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                   (uabT13c_evq_Zpos2 D D_pos energy) s')
                (mult (@evq_boltzmann_dist_attn bool uab_t2sum D D_pos energy
                         (uabT13c_evq_Zpos2 D D_pos energy) s) c)).
Proof.
  intros D D_pos energy c s s'.
  (* controlled unfolding at the definition level: dist_attn unfolds to
  the raw scaled-product family, the req swap lemma is instantiated on
  the bare products (named witnesses), and the unfolded face closes by
  conversion *)
  unfold evq_boltzmann_dist_attn.
  pose proof (uabT13c_swap_req_gen
                (fun x : bool =>
                   mult (inv_pos
                           (@evq_Z_thermo bool uab_t2sum D D_pos energy)
                           (uabT13c_evq_Zpos2 D D_pos energy))
                        (@evq_boltzmann_factor bool D D_pos energy x))
                c s s') as Hswap.
  exact Hswap.
Qed.

End UabT13cG13Req.

(* ---- closing audit ---- *)
Print Assumptions uabT13c_evict61.
Print Assumptions uabT13c_evict87.
Print Assumptions uabT13c_evict68.
Print Assumptions uabT13c_evict71.
Print Assumptions uabT13c_evq_norm464.
Print Assumptions uabT13c_evq_db468.
(* -- supplementary assumption audit for the helper lemmas (all should
   report Closed under the global context) -- *)
Print Assumptions uabT13c_swap_id_gen.
Print Assumptions uabT13c_swap_req_gen.
Print Assumptions uabT13c_half_row.
