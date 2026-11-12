(* ===================================================================== *)
(* ConstructiveWorld-Main - planB wave-2 G1: Laurent pole-coefficient extraction face (ZZ2020 Lemma 1 A_{n,j}/B_{n,j} general-n readout). *)
(** * planb4_g1_laur_extract: ascending power-series division and the
    A/B pole extraction it feeds.

    Mission.  [planb4_g1_laur num den k] reads k coefficients of
    num/den as a power series: step [a := hd rem 0 / d0], tail update
    [rem'(i) := rem(i+1) - a*den(i+1)].  Family faces:
    np = 5*x^{2n}(x^4+6x^2+25)^{2n}, dp = (25-x^2)^{3n+1},
    pq = polynomial part, shp/shm = N(5-w), N(w-5), denw = (10-w)^{3n+1},
    poleA/poleB n j = nth (3n-j) of the Laurent readout, j = 0..3n,
    i.e. A_j = [w^{3n-j}](N(5-w)/(10-w)^{3n+1}).  DOMAIN HONESTY: no
    forall-n statement lives here; every claim reaches exactly its
    anchor point - three small laur literals, the n = 1..6 family
    against the zzm1b certified zz_as/zz_bs/zz_pq tables, and
    poleA = poleB on the same window, sampled further at n = 7..11.

    Dependencies.  zzm2_qpoly (pdivmod, pshift_gen, ppow, pscal,
    plq_eqb); zzm1b_linform_bridge (certified tables, zz_lqeqb);
    zzm1_gauss (zzId).

    References.  ZZ2020 Lemma 1; the head entry N(5)/10^{3n+1}
    re-derives the zzm1b zz_closed literals for n = 1..6.

    Constructivity.  Transparent Fixpoints/Definitions over Q lists;
    no non-constructive escapes; every claim fully discharged; zero Prop-bearing statement (zzId form).

    Build.  coqc -native-compiler no -q -Q . "" planb4_g1_laur_extract.v
    (Rocq 9.3.0; zzm trust-cache .vo consumed in this directory). *)

From Stdlib Require Import QArith.QArith QArith.Qcanon ZArith.ZArith List.
Import ListNotations.
Require Import zzm1_gauss.
Require Import zzm1b_linform_bridge.
Require Import zzm2_qpoly.

Open Scope Q_scope.


(* ============================================================ *)
(* §1 Laurent power-series division (Set-borne, all Defined)     *)
(* ============================================================ *)

(* Tail update rem'(i) := rem(i+1) - a*den(i+1): absent entries read
   as 0, so the result length is max(len r, len d).  Keeping den's
   tail alive after rem's list runs dry is exactly what makes the
   later coefficients (e.g. of w/(1+2w)) come out nonzero.  Fuel
   style (pdiv_go family); the wrapper fuels with len r + len d,
   which always covers the max length the update can produce.
   Every produced entry is Qred-normalized: the base-Q ring ops
   multiply denominators without gcd reduction, so without Qred the
   per-step fraction sizes compound multiplicatively and the chain
   at n >= 3 drowns in huge numerals (the small anchors n <= 2 pass
   and n >= 3 hang - the family anchors caught this fail-loud). *)
Fixpoint planb4_g1_laur_sub_go (a : Q) (fuel : nat) (r d : list Q) : list Q :=
  match fuel with
  | O => nil
  | S f =>
      match r, d with
      | nil, nil => nil
      | nil, y :: d' => (Qred (0%Q - (a * y)%Q))%Q :: planb4_g1_laur_sub_go a f nil d'
      | x :: r', nil => x :: planb4_g1_laur_sub_go a f r' nil
      | x :: r', y :: d' => (Qred (x - (a * y)%Q))%Q :: planb4_g1_laur_sub_go a f r' d'
      end
  end.

Definition planb4_g1_laur_sub (a : Q) (r d : list Q) : list Q :=
  planb4_g1_laur_sub_go a (length r + length d)%nat r d.

(* Stepper: one quotient coefficient per step, k steps total.
   Precondition for meaningful output: d0 = hd den 0 <> 0 (the family
   denw n has d0 = 10^{3n+1} <> 0). *)
Fixpoint planb4_g1_laur_go (den : list Q) (d0 : Q) (k : nat) (rem : list Q)
  : list Q :=
  match k with
  | O => nil
  | S k' =>
      let a := (Qred (hd 0%Q rem / d0))%Q in
      a :: planb4_g1_laur_go den d0 k' (planb4_g1_laur_sub a (tl rem) (tl den))
  end.

(* Main entry: k leading power-series coefficients of num/den. *)
Definition planb4_g1_laur (num den : list Q) (k : nat) : list Q :=
  planb4_g1_laur_go den (hd 0%Q den) k num.


(* ============================================================ *)
(* §2 Family faces (slice-2 kernels, all Defined)                *)
(* ============================================================ *)

Definition planb4_g1_np (n : nat) : list Q := pscal (ppow zz2_pQ (2 * n)%nat) 5%Q.
Definition planb4_g1_dp (n : nat) : list Q := ppow zz2_pD ((3 * n + 1)%nat).
Definition planb4_g1_pq (n : nat) : list Q :=
  fst (pdivmod (planb4_g1_np n) (planb4_g1_dp n)).
Definition planb4_g1_shp (n : nat) : list Q := pshift_gen (planb4_g1_np n) [5%Q; -1%Q].
Definition planb4_g1_shm (n : nat) : list Q := pshift_gen (planb4_g1_np n) [-5%Q; 1%Q].
Definition planb4_g1_denw (n : nat) : list Q := ppow [10%Q; -1%Q] ((3 * n + 1)%nat).

(* A_{n,j} = [w^{3n-j}](N(5-w)/(10-w)^{3n+1}), j = 0..3n, read off the
   Laurent series with the highest w-power first. *)
Definition planb4_g1_poleA (n : nat) : list Q :=
  map (fun j => nth ((3 * n - j)%nat)
             (planb4_g1_laur (planb4_g1_shp n) (planb4_g1_denw n)
                             ((3 * n + 1)%nat)) 0%Q)
      (seq 0 ((3 * n + 1)%nat)).

(* B channel, same structure at the antipode (numerator N(w-5)). *)
Definition planb4_g1_poleB (n : nat) : list Q :=
  map (fun j => nth ((3 * n - j)%nat)
             (planb4_g1_laur (planb4_g1_shm n) (planb4_g1_denw n)
                             ((3 * n + 1)%nat)) 0%Q)
      (seq 0 ((3 * n + 1)%nat)).


(* ============================================================ *)
(* §3 Small literal anchors for the Laurent divider (x3)          *)
(* ============================================================ *)

(* (1+2w)/(1+w) = 1 + w - w^2 + w^3 + O(w^4). *)
Lemma zz3_small_laur_div1 :
  zzId (plq_eqb (planb4_g1_laur [(1#1)%Q; (2#1)%Q] [(1#1)%Q; (1#1)%Q] 4)
                [(1#1)%Q; (1#1)%Q; (-1#1)%Q; (1#1)%Q]) true.
Proof. vm_compute. reflexivity. Qed.

(* 1/2 is a polynomial: the readout dies after the constant term. *)
Lemma zz3_small_laur_inv :
  zzId (plq_eqb (planb4_g1_laur [(1#1)%Q] [(2#1)%Q] 3)
                [(1#2)%Q; (0#1)%Q; (0#1)%Q]) true.
Proof. vm_compute. reflexivity. Qed.

(* w/(1+2w) = w - 2w^2 + 4w^3 - 8w^4 + O(w^5): the coefficient -2 of
   w^2 is produced while rem's list is already dry - the absent-entry
   branch of the tail update carries den's contribution. *)
Lemma zz3_small_laur_shift :
  zzId (plq_eqb (planb4_g1_laur [(0#1)%Q; (1#1)%Q] [(1#1)%Q; (2#1)%Q] 4)
                [(0#1)%Q; (1#1)%Q; (-2#1)%Q; (4#1)%Q]) true.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* §4 Family anchors n = 1..6 (machine chain vs certified tables) *)
(* ============================================================ *)

Lemma zz3_poleA_1 : zzId (plq_eqb (planb4_g1_poleA 1) zz_as_1) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_poleB_1 : zzId (plq_eqb (planb4_g1_poleB 1) zz_bs_1) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_pq_1 : zzId (plq_eqb (planb4_g1_pq 1) zz_pq_1) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_1 : zzId (zz_lqeqb (planb4_g1_poleA 1) (planb4_g1_poleB 1)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz3_poleA_2 : zzId (plq_eqb (planb4_g1_poleA 2) zz_as_2) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_poleB_2 : zzId (plq_eqb (planb4_g1_poleB 2) zz_bs_2) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_pq_2 : zzId (plq_eqb (planb4_g1_pq 2) zz_pq_2) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_2 : zzId (zz_lqeqb (planb4_g1_poleA 2) (planb4_g1_poleB 2)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz3_poleA_3 : zzId (plq_eqb (planb4_g1_poleA 3) zz_as_3) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_poleB_3 : zzId (plq_eqb (planb4_g1_poleB 3) zz_bs_3) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_pq_3 : zzId (plq_eqb (planb4_g1_pq 3) zz_pq_3) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_3 : zzId (zz_lqeqb (planb4_g1_poleA 3) (planb4_g1_poleB 3)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz3_poleA_4 : zzId (plq_eqb (planb4_g1_poleA 4) zz_as_4) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_poleB_4 : zzId (plq_eqb (planb4_g1_poleB 4) zz_bs_4) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_pq_4 : zzId (plq_eqb (planb4_g1_pq 4) zz_pq_4) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_4 : zzId (zz_lqeqb (planb4_g1_poleA 4) (planb4_g1_poleB 4)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz3_poleA_5 : zzId (plq_eqb (planb4_g1_poleA 5) zz_as_5) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_poleB_5 : zzId (plq_eqb (planb4_g1_poleB 5) zz_bs_5) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_pq_5 : zzId (plq_eqb (planb4_g1_pq 5) zz_pq_5) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_5 : zzId (zz_lqeqb (planb4_g1_poleA 5) (planb4_g1_poleB 5)) true.
Proof. vm_compute. reflexivity. Qed.

Lemma zz3_poleA_6 : zzId (plq_eqb (planb4_g1_poleA 6) zz_as_6) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_poleB_6 : zzId (plq_eqb (planb4_g1_poleB 6) zz_bs_6) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_pq_6 : zzId (plq_eqb (planb4_g1_pq 6) zz_pq_6) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_6 : zzId (zz_lqeqb (planb4_g1_poleA 6) (planb4_g1_poleB 6)) true.
Proof. vm_compute. reflexivity. Qed.

(* Antipodal symmetry read directly off the two Laurent chains: the
   5 <-> -5 numerator swap (shp vs shm) must land on the same
   coefficient list over the same denw.  Sampled at n = 7..11,
   beyond the certified table window - each anchor is an
   independent vm_compute check, droppable to bound the shot time. *)
Lemma zz3_sym_7 : zzId (zz_lqeqb (planb4_g1_poleA 7) (planb4_g1_poleB 7)) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_8 : zzId (zz_lqeqb (planb4_g1_poleA 8) (planb4_g1_poleB 8)) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_9 : zzId (zz_lqeqb (planb4_g1_poleA 9) (planb4_g1_poleB 9)) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_10 : zzId (zz_lqeqb (planb4_g1_poleA 10) (planb4_g1_poleB 10)) true.
Proof. vm_compute. reflexivity. Qed.
Lemma zz3_sym_11 : zzId (zz_lqeqb (planb4_g1_poleA 11) (planb4_g1_poleB 11)) true.
Proof. vm_compute. reflexivity. Qed.


(* ============================================================ *)
(* §5 Extraction and audit                                       *)
(* ============================================================ *)

From Stdlib Require Import Extraction.
Separate Extraction planb4_g1_laur planb4_g1_laur_go planb4_g1_laur_sub
  planb4_g1_laur_sub_go Qred
  planb4_g1_np planb4_g1_dp planb4_g1_pq planb4_g1_shp planb4_g1_shm
  planb4_g1_denw planb4_g1_poleA planb4_g1_poleB.

Print Assumptions zz3_small_laur_div1.
Print Assumptions zz3_small_laur_inv.
Print Assumptions zz3_small_laur_shift.
Print Assumptions zz3_poleA_1.
Print Assumptions zz3_poleB_1.
Print Assumptions zz3_pq_1.
Print Assumptions zz3_sym_1.
Print Assumptions zz3_poleA_2.
Print Assumptions zz3_poleB_2.
Print Assumptions zz3_pq_2.
Print Assumptions zz3_sym_2.
Print Assumptions zz3_poleA_3.
Print Assumptions zz3_poleB_3.
Print Assumptions zz3_pq_3.
Print Assumptions zz3_sym_3.
Print Assumptions zz3_poleA_4.
Print Assumptions zz3_poleB_4.
Print Assumptions zz3_pq_4.
Print Assumptions zz3_sym_4.
Print Assumptions zz3_poleA_5.
Print Assumptions zz3_poleB_5.
Print Assumptions zz3_pq_5.
Print Assumptions zz3_sym_5.
Print Assumptions zz3_poleA_6.
Print Assumptions zz3_poleB_6.
Print Assumptions zz3_pq_6.
Print Assumptions zz3_sym_6.
Print Assumptions zz3_sym_7.
Print Assumptions zz3_sym_8.
Print Assumptions zz3_sym_9.
Print Assumptions zz3_sym_10.
Print Assumptions zz3_sym_11.
