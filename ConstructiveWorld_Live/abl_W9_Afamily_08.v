(* ========================================================================== *)
(*  abl_W9_Afamily_08.v - A-family numeric-index-boundary ablation batch     *)
(* ========================================================================== *)
(*   Mission. 38 stations: numeric witnesses abl08_idx1/idx0/idx2            *)
(*   (NatLe 1 1 / NatLe 0 0 / NatLe (2 * 1) 2) plus 34 numeric instantiations*)
(*   of the A-class numeric-index-boundary slots of S10_KVQuantTrig:         *)
(*   premise slots (1 <= n)%nat / (1 <= m)%nat / (1 <= d)%nat / (1 <= k)%nat *)
(*   / (1 <= J)%nat + associates (i <= m-1)%nat / (d <= n)%nat / (2*d <=     *)
(*   n)%nat hold at n:=1, m:=1, d:=1, k:=1, J:=1 (i:=0, n:=1, n:=2); the     *)
(*   premise-carrying theorems assemble into index-free corollaries, source  *)
(*   proof bodies (longest 93 lines) inherited wholesale. Statement faces    *)
(*   carry the canonical Set forms QleT' / QltT / QeqT / NatLe; proofs       *)
(*   route through the registered bridges (QleT'_to_Qle, QltT_to_Qlt,        *)
(*   NatLe_drop) measured against the current tree signatures. Coverage:     *)
(*   33 of 36 A-class slots; the other 3 (cos_abs_lift L7942 /               *)
(*   approx_def_test_cos L7953 B-face, two pointwise / composite slots)      *)
(*   recorded, not discharged.                                               *)
(*   Dependencies. Stdlib QArith (QArith, Qabs, Qround), ZArith, Extraction; *)
(*   chain pieces S01_BaseRing, S02_CauchyComplete (canonical Set faces +    *)
(*   bridges), S03_QExp, S10_KVQuantTrig (world .v byte-equal to Live).      *)
(*   References. ConstructiveWorld_Live/S10_KVQuantTrig.v (read-only source  *)
(*   comparison; anchors in per-piece comments); precedent abl_W9_pi_widen_13 *)
(*   Constructivity. Purely constructive; no classical faces; zero           *)
(*   admission word faces; all pieces closed by [Qed]; tail [Print           *)
(*   Assumptions] all Closed (37 statements); extraction [Obj.magic] 0.      *)
(*   Build. [rocq c -native-compiler no -q -Q . "" abl_W9_Afamily_08.v] in   *)
(*   the seat world closure; wrapped by cpu_guard (-Reg /tmp/cw_reg_nw4      *)
(*   -Front 0 -Mid 1 -MaxWaitSec 600) with [ulimit -s 65532].                *)
(* ========================================================================== *)

From Stdlib Require Import QArith.QArith QArith.Qabs QArith.Qround ZArith.
From Stdlib Require Import Extraction.
Require Import S01_BaseRing.
Require Import S02_CauchyComplete.
Require Import S03_QExp.
Require Import S10_KVQuantTrig.

(* ============================================================ *)
(* Part 0 - Numeric instance witnesses (minimal numeric          *)
(* instances of the index-bound premise slots)                   *)
(* ============================================================ *)

Lemma abl08_idx1 : NatLe 1 1.
Proof. exact (NatLe_lift 1 1 (le_n 1)). Qed.

Lemma abl08_idx0 : NatLe 0 0.
Proof. exact (NatLe_lift 0 0 (le_n 0)). Qed.

Lemma abl08_idx2 : NatLe (2 * 1)%nat 2.
Proof. exact (NatLe_lift (2 * 1)%nat 2 (le_n 2)). Qed.

(* ============================================================ *)
(* Part 1 - Slice-1 core targets (coverage table, slice-1        *)
(* eight slots)                                                  *)
(* ============================================================ *)

(* Coverage: sc_qpow_lt L4040 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_qpow_lt_i1 : forall x y : Q,
  QleT' 0 x -> QltT x y -> QltT (q_pow x 1) (q_pow y 1).
Proof.
  intros x y Hx Hxy.
  exact (sc_qpow_lt 1 x y (QleT'_to_Qle _ _ Hx) (QltT_to_Qlt _ _ Hxy)
                       (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_cs_eo_raw L5241 slot (1 <= m)%nat; numeric instance m:=1. *)
Theorem abl08_sc_cs_eo_raw_i1 :
  QeqT
    (sum_upto (1 + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * 1 - 2 * i))))
    (sum_upto 1 (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * 1 - 2 * i - 1)))).
Proof.
  exact (sc_cs_eo_raw 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_cs_dpair_form L5306 slot (1 <= m)%nat (associate slot
   (i <= m-1)%nat discharged by the same piece); numeric instances m:=1, i:=0. *)
Theorem abl08_sc_cs_dpair_form_i1 : forall t : Q,
  QeqT (sin_term 0 t * sin_term (1 - 1 - 0)%nat t)
       ((q_pow (-1) (1 - 1) * q_pow t (2 * 1)) *
          Qinv (q_fact (2 * 0 + 1) * q_fact (2 * 1 - 2 * 0 - 1))).
Proof.
  intro t.
  exact (sc_cs_dpair_form t 1 0 (NatLe_drop _ _ abl08_idx1) (NatLe_drop _ _ abl08_idx0)).
Qed.

(* Coverage: sc_cs_deg_van L5372 slot (1 <= m)%nat; numeric instance m:=1. *)
Theorem abl08_sc_cs_deg_van_i1 : forall t : Q,
  QeqT
    (sum_upto (1 + 1) (fun i : nat => cos_term i t * cos_term (1 - i)%nat t) +
     sum_upto 1 (fun i : nat => sin_term i t * sin_term (1 - 1 - i)%nat t))
    (0).
Proof.
  intro t. exact (sc_cs_deg_van t 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_cs_tri_d_eval L5534 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_cs_tri_d_eval_i1 : forall t : Q,
  QeqT
    (sum_upto 1 (fun j : nat => sum_upto (Datatypes.S (1 - 1 - j)) (fun i : nat => sin_term j t * sin_term i t)))
    (sum_upto 1 (fun k : nat =>
      (q_pow (-1) (Datatypes.S k - 1) * q_pow t (2 * (Datatypes.S k))) *
        sum_upto (Datatypes.S k) (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * (Datatypes.S k) - 2 * i - 1))))).
Proof.
  intro t. exact (sc_cs_tri_d_eval t 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_cs_d_tail_diff_le L5900 slot (1 <= d)%nat (associate slot
   (d <= n)%nat discharged by the same piece); numeric instances d:=1, n:=1. *)
Theorem abl08_sc_cs_d_tail_diff_le_i1 : forall (t B : Q),
  QleT' 0 B -> QleT' (Qabs t) B ->
  QleT' (sum_upto (Datatypes.S (1 - 1)) (fun m : nat => Qabs (sin_term (1 + m)%nat t)))
        (exp_series (2 * 1 + 1) B - exp_series (2 * 1 - 1) B).
Proof.
  intros t B H0 H1.
  exact (sc_cs_d_tail_diff_le t B 1 1 (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)
                                   (NatLe_drop _ _ abl08_idx1) (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_cs_sq_err_tail_le L6300 slot (1 <= d)%nat (associate slot
   (2*d <= n)%nat discharged by the same piece); numeric instances d:=1, n:=2. *)
Theorem abl08_sc_cs_sq_err_tail_le_i1 : forall (t B : Q),
  QleT' 0 B -> QleT' (Qabs t) B ->
  QleT' (Qabs (cos_partial 2 t * cos_partial 2 t + sin_partial 2 t * sin_partial 2 t - 1))
        (((1 + 1) * (1 + 1)) *
         (exp_series (2 * 2 + 1) B * exp_tail_abs (2 * 1 - 1) (2 * 2 + 1) B)).
Proof.
  intros t B H0 H1.
  exact (sc_cs_sq_err_tail_le t B 1 2 (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)
                                      (NatLe_drop _ _ abl08_idx1) (NatLe_drop _ _ abl08_idx2)).
Qed.

(* Coverage: sc_A_succ_bound L6946 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_A_succ_bound_i1 : forall p q : Q,
  QleT' 0 p -> QleT' p q -> QleT' q 4 ->
  QleT' (q * sc_A p q 1 + q_pow p 1)
        (((Z.of_nat (2 * 1 + 1) * Z.of_nat (2 * 1 + 2)) # 1) * sc_A p q 1).
Proof.
  intros p q H0 H1 H2.
  exact (sc_A_succ_bound p q 1 (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)
                               (QleT'_to_Qle _ _ H2) (NatLe_drop _ _ abl08_idx1)).
Qed.

(* ============================================================ *)
(* Part 2 - Slice-1 supplementary targets (coverage table        *)
(* names: sc_A_ge family / sc_t_dec / sc_add_sin family)         *)
(* ============================================================ *)

(* Coverage: sc_A_ge_q L6828 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_A_ge_q_i1 : forall p q : Q,
  QleT' 0 p -> QleT' 0 q -> QleT' (q_pow q (1 - 1)) (sc_A p q 1).
Proof.
  intros p q H0 H1.
  exact (sc_A_ge_q p q 1 (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)
                         (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_A_ge_p L6850 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_A_ge_p_i1 : forall p q : Q,
  QleT' 0 p -> QleT' 0 q -> QleT' (q_pow p (1 - 1)) (sc_A p q 1).
Proof.
  intros p q H0 H1.
  exact (sc_A_ge_p p q 1 (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)
                         (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_t_dec L6994 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_t_dec_i1 : forall p q : Q,
  QleT' 0 p -> QleT' p q -> QleT' q 4 ->
  QleT' (sc_A p q (Datatypes.S 1) / q_fact (2 * Datatypes.S 1))
        (sc_A p q 1 / q_fact (2 * 1)).
Proof.
  intros p q H0 H1 H2.
  exact (sc_t_dec p q 1 (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)
                        (QleT'_to_Qle _ _ H2) (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_add_sin_err_abs L10946 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_add_sin_err_abs_i1 : forall (x y : Q) (B : Q),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sin_partial (2 * 1) (x + y) - sin_partial 1 x * cos_partial 1 y - cos_partial 1 x * sin_partial 1 y))
        (((1 + 1) * (1 + 1)) * (exp_series (2 * 1 + 1) B * (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B))).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_sin_err_abs x y 1 B (NatLe_drop _ _ abl08_idx1)
                                    (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ Hx)
                                    (QleT'_to_Qle _ _ Hy)).
Qed.

(* ============================================================ *)
(* Part 3 - Slice-2 core targets (coverage table slice-2         *)
(* five slots: sc_add_cos family)                                *)
(* ============================================================ *)

(* Coverage: sc_add_cos_diag_swap L11402 slot (1 <= J)%nat; numeric instance J:=1. *)
Theorem abl08_sc_add_cos_diag_swap_i1 : forall x y : Q,
  QeqT (cos_partial 1 (x + y))
       ((sum_upto (Datatypes.S 1) (fun i : nat => sum_upto (Datatypes.S (1 - i)) (fun k : nat => cos_term i x * cos_term k y))) -
        (sum_upto (Datatypes.S (1 - 1)) (fun i : nat => sum_upto (Datatypes.S (1 - 1 - i)) (fun k : nat => sin_term i x * sin_term k y)))).
Proof.
  intros x y. exact (sc_add_cos_diag_swap x y 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage: sc_add_cos_err_decomp L11445 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_add_cos_err_decomp_i1 : forall x y : Q,
  QeqT
    (cos_partial (2 * 1) (x + y) - cos_partial 1 x * cos_partial 1 y + sin_partial 1 x * sin_partial 1 y)
    ((sum_upto (Datatypes.S 1) (fun j : nat => sum_upto (1 - j) (fun k : nat => cos_term j x * cos_term ((Datatypes.S 1 + k)%nat) y)) +
      sum_upto 1 (fun j : nat => sum_upto (Datatypes.S (2 * 1 - Datatypes.S 1 - j)) (fun i : nat => cos_term ((Datatypes.S 1 + j)%nat) x * cos_term i y))) -
     (sum_upto (Datatypes.S 1) (fun j : nat => sum_upto (1 - j) (fun k : nat => sin_term j x * sin_term ((Datatypes.S 1 + k)%nat) y)) +
      sum_upto 1 (fun j : nat => sum_upto (Datatypes.S (2 * 1 - Datatypes.S 1 - j)) (fun i : nat => sin_term ((Datatypes.S 1 + j)%nat) x * sin_term i y))) +
     sum_upto (Datatypes.S (2 * 1)) (fun i : nat => sin_term i x * sin_term ((2 * 1 - i)%nat) y)).
Proof.
  intros x y. exact (sc_add_cos_err_decomp x y 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* Coverage head target: sc_add_cos_anti_le L11716 slot (1 <= n)%nat
   (93-line proof body, one of the 13 W-A spot-check slots); numeric
   instance n:=1. *)
Theorem abl08_sc_add_cos_anti_le_i1 : forall (x y : Q) (B : Q),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sum_upto (Datatypes.S (2 * 1)) (fun i : nat => sin_term i x * sin_term ((2 * 1 - i)%nat) y)))
        (exp_series (2 * 1 + 1) B * (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1)) +
         (1 + 1) * (exp_series (2 * 1 + 1) B * (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B))).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_cos_anti_le x y 1 B (NatLe_drop _ _ abl08_idx1)
                                    (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ Hx)
                                    (QleT'_to_Qle _ _ Hy)).
Qed.

(* Coverage: sc_add_cos_err_abs L11869 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_add_cos_err_abs_i1 : forall (x y : Q) (B : Q),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (cos_partial (2 * 1) (x + y) - cos_partial 1 x * cos_partial 1 y + sin_partial 1 x * sin_partial 1 y))
        (exp_series (2 * 1 + 1) B * (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1)) +
         ((1 + 1) * (1 + 1 + 1)) * (exp_series (2 * 1 + 1) B * (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B))).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_cos_err_abs x y 1 B (NatLe_drop _ _ abl08_idx1)
                                    (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ Hx)
                                    (QleT'_to_Qle _ _ Hy)).
Qed.

(* Slice-2 named: sc_add_cos_err_tail_le L11949 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_add_cos_err_tail_le_i1 : forall (x y : Q) (B : Q),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (cos_partial (2 * 1) (x + y) - cos_partial 1 x * cos_partial 1 y + sin_partial 1 x * sin_partial 1 y))
        (exp_series (2 * 1 + 1) B * (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1)) +
         ((1 + 1) * (1 + 1 + 1)) * (exp_series (2 * 1 + 1) B * exp_tail_abs (2 * 1 + 1) (4 * 1 + 1) B)).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_cos_err_tail_le x y 1 B (NatLe_drop _ _ abl08_idx1)
                                        (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ Hx)
                                        (QleT'_to_Qle _ _ Hy)).
Qed.

(* ============================================================ *)
(* Part 4 - Bulk remainder (coverage table remaining slice-1/2   *)
(* slots, A-slots checked one by one)                            *)
(* ============================================================ *)

(* sc_q_pow_zero_ge1 L2110 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_q_pow_zero_ge1_i1 : QeqT (q_pow 0 1) (0).
Proof.
  exact (sc_q_pow_zero_ge1 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_sin_alt_hlt L3362 slot 2 (1 <= j)%nat; numeric instance j:=1. *)
Theorem abl08_sc_sin_alt_hlt_i1 : forall x : Q,
  QleT' x 1 -> QltT (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 2)) 1).
Proof.
  intro x. intro H.
  exact (sc_sin_alt_hlt x 1 (QleT'_to_Qle _ _ H) (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_cos_alt_hlt L3371 slot 2 (1 <= j)%nat; numeric instance j:=1. *)
Theorem abl08_sc_cos_alt_hlt_i1 : forall x : Q,
  QleT' x 1 -> QltT (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 1)) 1).
Proof.
  intro x. intro H.
  exact (sc_cos_alt_hlt x 1 (QleT'_to_Qle _ _ H) (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_sin_alt_decr L3381 slot 2 (1 <= j)%nat; numeric instance j:=1. *)
Theorem abl08_sc_sin_alt_decr_i1 : forall x : Q,
  QleT' 0 x -> QltT (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 2)) 1) ->
  QleT' (sc_sin_alt (Datatypes.S 1) x) (sc_sin_alt 1 x).
Proof.
  intros x H0 H1.
  exact (sc_sin_alt_decr x 1 (QleT'_to_Qle _ _ H0) (NatLe_drop _ _ abl08_idx1)
                             (QltT_to_Qlt _ _ H1)).
Qed.

(* sc_cos_alt_decr L3402 slot 2 (1 <= j)%nat; numeric instance j:=1. *)
Theorem abl08_sc_cos_alt_decr_i1 : forall x : Q,
  QleT' 0 x -> QltT (Qmult (1 + 1)%Q x) (Qmake (Z.of_nat (2 * 1 + 1)) 1) ->
  QleT' (sc_cos_alt (Datatypes.S 1) x) (sc_cos_alt 1 x).
Proof.
  intros x H0 H1.
  exact (sc_cos_alt_decr x 1 (QleT'_to_Qle _ _ H0) (NatLe_drop _ _ abl08_idx1)
                             (QltT_to_Qlt _ _ H1)).
Qed.

(* sc_sin_odd_ge3 L4102 slot (1 <= m)%nat; numeric instance m:=1. *)
Theorem abl08_sc_sin_odd_ge3_i1 : forall x : Q,
  QleT' 0 x -> QleT' x 1 -> QleT' (sin_partial 3 x) (sin_partial (Datatypes.S (2 * 1)) x).
Proof.
  intros x H0 H1.
  exact (sc_sin_odd_ge3 1 x (NatLe_drop _ _ abl08_idx1)
                            (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)).
Qed.

(* sc_cos_odd_ge3 L4421 slot (1 <= m)%nat; numeric instance m:=1. *)
Theorem abl08_sc_cos_odd_ge3_i1 : forall x : Q,
  QleT' 0 x -> QleT' x 1 -> QleT' (cos_partial 3 x) (cos_partial (Datatypes.S (2 * 1)) x).
Proof.
  intros x H0 H1.
  exact (sc_cos_odd_ge3 1 x (NatLe_drop _ _ abl08_idx1)
                            (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)).
Qed.

(* sc_cs_ddeg_sum L5355 slot (1 <= m)%nat; numeric instance m:=1. *)
Theorem abl08_sc_cs_ddeg_sum_i1 : forall t : Q,
  QeqT
    (sum_upto 1 (fun i : nat => sin_term i t * sin_term (1 - 1 - i)%nat t))
    ((q_pow (-1) (1 - 1) * q_pow t (2 * 1)) *
     sum_upto 1 (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * 1 - 2 * i - 1)))).
Proof.
  intro t. exact (sc_cs_ddeg_sum t 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_cs_deg_van_x L5503 slot (1 <= m)%nat; numeric instance m:=1. *)
Theorem abl08_sc_cs_deg_van_x_i1 : forall t : Q,
  QeqT
    ((q_pow (-1) 1 * q_pow t (2 * 1)) *
       sum_upto (1 + 1) (fun i : nat => Qinv (q_fact (2 * i) * q_fact (2 * 1 - 2 * i))) +
     (q_pow (-1) (1 - 1) * q_pow t (2 * 1)) *
       sum_upto 1 (fun i : nat => Qinv (q_fact (2 * i + 1) * q_fact (2 * 1 - 2 * i - 1))))
    (0).
Proof.
  intro t. exact (sc_cs_deg_van_x t 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_sin_alt_hlt2 L6537 slot 2 (1 <= j)%nat; numeric instance j:=1. *)
Theorem abl08_sc_sin_alt_hlt2_i1 : forall x : Q,
  QltT x 2 -> QltT (Qmult (1 + 1) x) (Qmake (Z.of_nat (2 * 1 + 2)) 1).
Proof.
  intro x. intro H.
  exact (sc_sin_alt_hlt2 x 1 (QltT_to_Qlt _ _ H) (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_M_ge8 L6895 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_M_ge8_i1 : QleT' 8 ((Z.of_nat (2 * 1 + 1) * Z.of_nat (2 * 1 + 2)) # 1).
Proof.
  exact (sc_M_ge8 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_q_pow_pred L7225 slot (1 <= k)%nat; numeric instance k:=1. *)
Theorem abl08_sc_q_pow_pred_i1 : QeqT (q_pow (-1) 1 * -1) (q_pow (-1) (1 - 1)).
Proof.
  exact (sc_q_pow_pred 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_add_neg_sign L10022 slot (1 <= j)%nat; numeric instance j:=1. *)
Theorem abl08_sc_add_neg_sign_i1 : QeqT (q_pow (-1) 1) (- q_pow (-1) (1 - 1)).
Proof.
  exact (sc_add_neg_sign 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_add_d_tail_le L10912 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_add_d_tail_le_i1 : forall (t B : Q),
  QleT' 0 B -> QleT' (Qabs t) B ->
  QleT' (sum_upto 1 (fun m : nat => Qabs (sin_term ((Datatypes.S 1 + m)%nat) t)))
        (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B).
Proof.
  intros t B H0 H1.
  exact (sc_add_d_tail_le t B 1 (NatLe_drop _ _ abl08_idx1)
                                (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)).
Qed.

(* sc_add_sin_err_tail_le L11044 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_add_sin_err_tail_le_i1 : forall (x y : Q) (B : Q),
  QleT' 0 B -> QleT' (Qabs x) B -> QleT' (Qabs y) B ->
  QleT' (Qabs (sin_partial (2 * 1) (x + y) - sin_partial 1 x * cos_partial 1 y - cos_partial 1 x * sin_partial 1 y))
        (((1 + 1) * (1 + 1)) * (exp_series (2 * 1 + 1) B * exp_tail_abs (2 * 1 + 1) (4 * 1 + 1) B)).
Proof.
  intros x y B H0 Hx Hy.
  exact (sc_add_sin_err_tail_le x y 1 B (NatLe_drop _ _ abl08_idx1)
                                        (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ Hx)
                                        (QleT'_to_Qle _ _ Hy)).
Qed.

(* sc_add_cos_ss_swap L11384 slot (1 <= J)%nat; numeric instance J:=1. *)
Theorem abl08_sc_add_cos_ss_swap_i1 : forall x y : Q,
  QeqT
    (sum_upto (Datatypes.S 1) (fun j : nat => sum_upto j (fun i : nat => sin_term i x * sin_term (Nat.sub (Nat.sub j 1) i) y)))
    (sum_upto (Datatypes.S (1 - 1)) (fun i : nat => sum_upto (Datatypes.S (1 - 1 - i)) (fun k : nat => sin_term i x * sin_term k y))).
Proof.
  intros x y. exact (sc_add_cos_ss_swap x y 1 (NatLe_drop _ _ abl08_idx1)).
Qed.

(* sc_cos_add_W_le L11652 slot (1 <= n)%nat; numeric instance n:=1. *)
Theorem abl08_sc_cos_add_W_le_i1 : forall (t B : Q),
  QleT' 0 B -> QleT' (Qabs t) B ->
  QleT' (sum_upto (Datatypes.S 1) (fun m : nat => Qabs (sin_term ((1 + m)%nat) t)))
        (q_pow B (2 * 1 + 1) / q_fact (2 * 1 + 1) +
         (exp_series (4 * 1 + 1) B - exp_series (2 * 1 + 1) B)).
Proof.
  intros t B H0 H1.
  exact (sc_cos_add_W_le t B 1 (NatLe_drop _ _ abl08_idx1)
                               (QleT'_to_Qle _ _ H0) (QleT'_to_Qle _ _ H1)).
Qed.

(* ============================================================ *)
(* Part 5 - Extractability check (informative faces +            *)
(* Obj.magic = 0)                                                *)
(* ============================================================ *)

Definition abl08_probe_pair (t : Q) : Q := sin_term 0 t * cos_term 0 t.

Recursive Extraction abl08_probe_pair.
Recursive Extraction abl08_sc_M_ge8_i1.

(* ============================================================ *)
(* Part 6 - Tail audit: Print Assumptions on all pieces          *)
(* (37 theorems, one by one)                                     *)
(* ============================================================ *)

Print Assumptions abl08_idx1.
Print Assumptions abl08_idx0.
Print Assumptions abl08_idx2.
Print Assumptions abl08_sc_qpow_lt_i1.
Print Assumptions abl08_sc_cs_eo_raw_i1.
Print Assumptions abl08_sc_cs_dpair_form_i1.
Print Assumptions abl08_sc_cs_deg_van_i1.
Print Assumptions abl08_sc_cs_tri_d_eval_i1.
Print Assumptions abl08_sc_cs_d_tail_diff_le_i1.
Print Assumptions abl08_sc_cs_sq_err_tail_le_i1.
Print Assumptions abl08_sc_A_succ_bound_i1.
Print Assumptions abl08_sc_A_ge_q_i1.
Print Assumptions abl08_sc_A_ge_p_i1.
Print Assumptions abl08_sc_t_dec_i1.
Print Assumptions abl08_sc_add_sin_err_abs_i1.
Print Assumptions abl08_sc_add_cos_diag_swap_i1.
Print Assumptions abl08_sc_add_cos_err_decomp_i1.
Print Assumptions abl08_sc_add_cos_anti_le_i1.
Print Assumptions abl08_sc_add_cos_err_abs_i1.
Print Assumptions abl08_sc_add_cos_err_tail_le_i1.
Print Assumptions abl08_sc_q_pow_zero_ge1_i1.
Print Assumptions abl08_sc_sin_alt_hlt_i1.
Print Assumptions abl08_sc_cos_alt_hlt_i1.
Print Assumptions abl08_sc_sin_alt_decr_i1.
Print Assumptions abl08_sc_cos_alt_decr_i1.
Print Assumptions abl08_sc_sin_odd_ge3_i1.
Print Assumptions abl08_sc_cos_odd_ge3_i1.
Print Assumptions abl08_sc_cs_ddeg_sum_i1.
Print Assumptions abl08_sc_cs_deg_van_x_i1.
Print Assumptions abl08_sc_sin_alt_hlt2_i1.
Print Assumptions abl08_sc_M_ge8_i1.
Print Assumptions abl08_sc_q_pow_pred_i1.
Print Assumptions abl08_sc_add_neg_sign_i1.
Print Assumptions abl08_sc_add_d_tail_le_i1.
Print Assumptions abl08_sc_add_sin_err_tail_le_i1.
Print Assumptions abl08_sc_add_cos_ss_swap_i1.
Print Assumptions abl08_sc_cos_add_W_le_i1.
