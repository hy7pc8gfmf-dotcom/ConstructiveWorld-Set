
type __ = Obj.t

type empty_set = |

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

val projT1 : ('a1, 'a2) sigT -> 'a1

val projT2 : ('a1, 'a2) sigT -> 'a2

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val max : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat :
 sig
  val leb : nat -> nat -> bool

  val max : nat -> nat -> nat
 end

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val mul : z -> z -> z

  val compare : z -> z -> comparison

  val of_nat : nat -> z

  val abs : z -> z
 end

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qlt_le_dec : q -> q -> sumbool

val qarchimedean : q -> positive

val qabs : q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

val natLe_lift : nat -> nat -> natLe

type qseq = nat -> q

val qlt_bool : q -> q -> bool

type qltT = bool id

val qlt_to_QltT : q -> q -> qltT

type qleT' = bool id

val qle_to_QleT' : q -> q -> qleT'

type qeqT = bool id

val qeq_imp_qeqT : q -> q -> qeqT

val qeq_imp_qle : q -> q -> qeqT -> qleT'

val qltT_0_1 : qltT

val qltT_0_2 : qltT

val qltT_0_3 : qltT

val qleT'_refl : q -> qleT'

val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT'

val qltT_leT' : q -> q -> qltT -> qleT'

val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT

val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT

val qleT'_plus_compat : q -> q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_plus_nonneg_rT : q -> q -> qleT' -> qleT'

val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT

val qltT_plus_leT'_ltT : q -> q -> q -> q -> qltT -> qleT' -> qltT

val qleT'_plus_ltT_ltT : q -> q -> q -> q -> qleT' -> qltT -> qltT

val qleT'_mult_compat_l : q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_mult_ltT_compat :
  q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT

val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT

val qeq_leT' : q -> q -> qeqT -> qleT'

val qabs_nonnegT : q -> qleT'

val qltT_plus_pos_r : q -> q -> qltT -> qltT -> qltT

val qltT_div_pos : q -> q -> qltT -> qltT -> qltT

val qltT_eq_compat_l : q -> q -> q -> qeqT -> qltT -> qltT

val qltT_eq_compat_r : q -> q -> q -> qeqT -> qltT -> qltT

val qltT_mult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

type real_eq = q -> qltT -> (nat, nat -> natLe -> qltT) sigT

val real_plus : real -> real -> real

val real_opp : real -> real

val real_zero : real

type real_lt = (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

type real_le = (real_lt, real_eq) or0

val real_lt_trans : real -> real -> real -> real_lt -> real_lt -> real_lt

val sum_abs_prefix : qseq -> nat -> q

val cauchy_bounded : qseq -> cauchy -> (q, nat -> qleT') sigT

val qeq_le : q -> q -> qeqT -> qleT'

val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT

val real_mult : real -> real -> real

val real_const : q -> real

val real_eq_refl : real -> real_eq

val real_eq_sym : real -> real -> real_eq -> real_eq

val real_eq_trans : real -> real -> real -> real_eq -> real_eq -> real_eq

val real_one : real

val real_eq_of_zero_diff : real -> real -> (nat -> qeqT) -> real_eq

val real_plus_comm : real -> real -> real_eq

val real_plus_zero : real -> real_eq

val real_plus_opp : real -> real_eq

val real_mult_comm : real -> real -> real_eq

val real_mult_assoc : real -> real -> real -> real_eq

val real_mult_one : real -> real_eq

val real_lt_eq_lt : real -> real -> real -> real_lt -> real_eq -> real_lt

val real_eq_lt_lt : real -> real -> real -> real_eq -> real_lt -> real_lt

val real_le_trans : real -> real -> real -> real_le -> real_le -> real_le

val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le

val q_pow : q -> nat -> q

val q_fact : nat -> q

val exp_partial : nat -> q -> q

val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT

val arch_decay : q -> q -> qleT' -> qltT -> (nat, qltT) sigT

val q_pow_fact2_nonneg : q -> nat -> qleT' -> qleT'

val exp_partial_cauchy :
  q -> q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

val exp_series : nat -> q -> q

val exp_partial_cauchy_bounded :
  q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q -> qleT'
  -> qltT) sigT

val exp_series_arch : q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT

val exp_partial_lipschitz :
  q -> q -> q -> nat -> qleT' -> qleT' -> qleT' -> qleT'

val cauchy_real_exp : real -> real

val cauchy_real_exp_zero : real_eq

val sum_upto : nat -> (nat -> q) -> q

val exp_partial_tail_small :
  q -> q -> qleT' -> qleT' -> (nat, nat -> natLe -> qltT) sigT

val cauchy_real_exp_pos : real -> real_lt

val real_abs : real -> real

val real_inv_pos : real -> real_lt -> real

val real_inv_pos_correct : real -> real_lt -> real_eq

module RealSetoid :
 sig
  val real_eq_le : real -> real -> real_eq -> real_le

  val real_lt_le_iff_req : real -> real -> (real_lt, real_eq) or0 -> real_le

  val real_eq_plus_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_opp_compat : real -> real -> real_eq -> real_eq

  val real_eq_mult_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq
 end

val exp_trunc_arch_seq :
  (nat -> q) -> (nat -> q) -> q -> q -> qleT' -> (nat -> qleT') -> (nat ->
  qleT') -> qltT -> (nat, nat -> natLe -> qltT) sigT

val cauchy_real_exp_plus : real -> real -> real_eq

val cauchy_real_exp_gt_one : real -> real_lt -> real_lt

val real_lt_opp_plus : real -> real -> real_lt -> real_lt

val real_mult_pos_compat : real -> real -> real_lt -> real_lt -> real_lt

val cauchy_real_exp_minus_one_pos : real -> real_lt -> real_lt

val cauchy_real_exp_wd : real -> real -> real_eq -> real_eq

val real_mult_minus_factor : real -> real -> real_eq

val cauchy_real_exp_mono : real -> real -> real_lt -> real_lt

val real_arch : real -> (nat, (natLe, real_lt) and0) sigT

val cauchy_real_exp_gt_const : nat -> real_lt

val log_mid_lt_b : q -> q -> qltT -> qltT

val log_a_lt_mid : q -> q -> qltT -> qltT

val real_abs_diff_le_lift : real -> real -> q -> q -> nat -> real_lt

val real_inv_unique : real -> real -> real -> real_eq -> real_eq -> real_eq

val exp_neg_recip : real -> real_lt -> real_eq

val real_const_pos : q -> qltT -> real_lt

val real_inv_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val q_eps16_pos : q -> qltT -> qltT

val q_eps16_posT : q -> qltT -> qltT

val log_testA_eps : real -> q -> q -> qltT -> q -> qltT -> bool

val log_testB_eps : real -> q -> q -> qltT -> q -> qltT -> bool

val log_m_eps : q -> q -> q

val log_d4_eps : q -> q

val log_K1_eps : q -> q -> qltT -> q -> qltT -> nat

val log_K2_eps : real -> q -> q -> qltT -> q -> qltT -> nat

val log_q_eps : q -> q -> qltT -> q -> qltT -> q

val log_r_eps : real -> q -> q -> qltT -> q -> qltT -> q

val log_testA_eps_true_lt : real -> q -> q -> qltT -> q -> qltT -> real_lt

val log_testB_eps_true_gt : real -> q -> q -> qltT -> q -> qltT -> real_lt

val log_test_mid_bound_eps :
  real -> q -> q -> qltT -> q -> qltT -> nat -> qleT'

val log_scan :
  real -> q -> q -> qltT -> q -> qltT -> nat -> (((q, q) prod, qltT) sigT,
  bool) prod

val log_scan_spec :
  real -> q -> q -> qltT -> q -> qltT -> nat -> real_lt -> real_lt -> ((bool
  id, (real_lt, (real_lt, qeqT) and0) and0) and0, (bool id, nat -> __ ->
  qleT') and0) or0

val exp_lower_q : real -> real_lt -> (nat, (natLe, real_lt) and0) sigT

val exp_upper_q : real -> real_lt -> (nat, (natLe, real_lt) and0) sigT

val log_lower : real -> real_lt -> q

val log_upper : real -> real_lt -> q

val q_neg_nat_lt_nat : nat -> nat -> qltT

val q_pow_arch : q -> q -> qleT' -> qltT -> (nat, qltT) sigT

val real_const_lt : q -> q -> qltT -> real_lt

val real_lt_pt_lt :
  real -> real -> real_lt -> (nat, nat -> natLe -> qltT) sigT

val log_mid_strict : q -> q -> qltT -> (qltT, qltT) and0

val exp_const_lt : q -> q -> qltT -> real_lt

val approx_span_pt :
  real -> q -> q -> qltT -> q -> q -> real_lt -> real_lt -> qleT' -> qleT' ->
  qleT' -> (nat -> qleT') -> (nat, nat -> natLe -> qleT') sigT

val len_mul_D : q -> q -> q -> q -> q -> nat -> qeqT -> qeqT

val real_abs_lift :
  q -> real -> q -> q -> nat -> qltT -> (nat -> natLe -> qleT') -> real_lt

val approx_const_lt :
  q -> q -> q -> q -> q -> q -> nat -> qltT -> qeqT -> qeqT -> qltT

val approx_def_test :
  real -> q -> q -> qltT -> nat -> (nat -> natLe -> qleT') -> real_lt

val approx_root :
  real -> real_lt -> q -> qltT -> (q, (qltT, (qltT, real_lt) and0) and0) sigT

val log_eps : nat -> q

val log_eps_pos : nat -> qltT

val log_seq : real -> real_lt -> nat -> q

val approx_root_pt_bound :
  real -> real_lt -> nat -> (nat, nat -> natLe -> qltT) sigT

val exp_pos_shape :
  real -> (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

val log_seq_cauchy : real -> real_lt -> cauchy

val cw_log : real -> real_lt -> real

val exp_series_arch_shape : q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT

val cw_log_exp_right : real -> real_lt -> real_eq

val real_lt_not_eq : real -> real -> real_lt -> real_eq not

val real_weak_trich : real -> real -> real_lt not -> real_lt not -> real_eq

val log_inv_one_thm : real_lt -> real_eq

val real_log_lt_mono :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_opp_lt_compat : real -> real -> real_lt -> real_lt

val real_opp_le_compat : real -> real -> real_le -> real_le

val real_lt_zero_one : real_lt

val real_log : real -> real_lt -> real

val real_log_one : real_lt -> real_eq

val real_opp_zero : real_eq

val real_log_wd : real -> real -> real_lt -> real_lt -> real_eq -> real_eq

val real_lt_le_bridge : real -> real -> real_lt -> real_le

val real_eq_le_bridge : real -> real -> real_eq -> real_le

val real_log_le_mono :
  real -> real -> real_lt -> real_lt -> real_le -> real_le

val hlogz_discharge : real -> real_lt -> real_le -> real_le

val hlogz_strict : real -> real_lt -> real_lt -> real_lt

val hlogz_opp_nonneg : real -> real_lt -> real_le -> real_le
