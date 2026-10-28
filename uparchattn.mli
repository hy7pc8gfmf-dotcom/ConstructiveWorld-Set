
type __ = Obj.t

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

val add : nat -> nat -> nat

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

type q = { qnum : z; qden : positive }

val qcompare : q -> q -> comparison

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qdiv : q -> q -> q

val qarchimedean : q -> positive

val qabs : q -> q

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type natLe = bool id

val natLe_lift : nat -> nat -> natLe

type qseq = nat -> q

type qltT = bool id

val qlt_to_QltT : q -> q -> qltT

type qleT' = bool id

val qle_to_QleT' : q -> q -> qleT'

type qeqT = bool id

val qeq_imp_qeqT : q -> q -> qeqT

val qeq_imp_qle : q -> q -> qeqT -> qleT'

val qltT_0_2 : qltT

val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT'

val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT

val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT

val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT

val qleT'_mult_ltT_compat :
  q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT

val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT

val qeq_leT' : q -> q -> qeqT -> qleT'

val qabs_nonnegT : q -> qleT'

val qltT_div_pos : q -> q -> qltT -> qltT -> qltT

val qltT_eq_compat_l : q -> q -> q -> qeqT -> qltT -> qltT

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

val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT

val real_mult : real -> real -> real

val real_const : q -> real

val real_eq_refl : real -> real_eq

val real_eq_sym : real -> real -> real_eq -> real_eq

val real_eq_trans : real -> real -> real -> real_eq -> real_eq -> real_eq

val real_one : real

val real_eq_of_zero_diff : real -> real -> (nat -> qeqT) -> real_eq

val real_plus_comm : real -> real -> real_eq

val real_plus_assoc : real -> real -> real -> real_eq

val real_plus_zero : real -> real_eq

val real_plus_opp : real -> real_eq

val real_mult_comm : real -> real -> real_eq

val real_mult_assoc : real -> real -> real -> real_eq

val real_mult_one : real -> real_eq

val real_mult_zero : real -> real_eq

val real_distrib : real -> real -> real -> real_eq

val real_le_refl : real -> real_le

val real_lt_eq_lt : real -> real -> real -> real_lt -> real_eq -> real_lt

val real_eq_lt_lt : real -> real -> real -> real_eq -> real_lt -> real_lt

val real_le_trans : real -> real -> real -> real_le -> real_le -> real_le

val real_lt_le_trans : real -> real -> real -> real_lt -> real_le -> real_lt

val real_le_lt_trans : real -> real -> real -> real_le -> real_lt -> real_lt

val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le

val real_lt_plus_compat :
  real -> real -> real -> real -> real_lt -> real_lt -> real_lt

val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT

val real_inv_pos : real -> real_lt -> real

val real_inv_pos_correct : real -> real_lt -> real_eq

val real_inv_pos_pos : real -> real_lt -> real_lt

module RealSetoid :
 sig
  val real_eq_le : real -> real -> real_eq -> real_le

  val real_lt_le_iff_req : real -> real -> (real_lt, real_eq) or0 -> real_le

  val real_eq_plus_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq

  val real_eq_mult_compat :
    real -> real -> real -> real -> real_eq -> real_eq -> real_eq
 end

val real_lt_opp_plus : real -> real -> real_lt -> real_lt

val real_mult_pos_compat : real -> real -> real_lt -> real_lt -> real_lt

val real_lt_zero_minus : real -> real -> real_lt -> real_lt

val real_arch : real -> (nat, (natLe, real_lt) and0) sigT

val real_inv_unique : real -> real -> real -> real_eq -> real_eq -> real_eq

val real_mult_lt_compat :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_mult_lt_compat_l :
  real -> real -> real -> real_lt -> real_lt -> real_lt

val real_inv_pos_lt_contra :
  real -> real -> real_lt -> real_lt -> real_lt -> real_lt

val real_lt_plus_translate : real -> real -> real -> real_lt -> real_lt

val real_lt_plus_compat_lt_le :
  real -> real -> real -> real -> real_lt -> real_le -> real_lt

val real_le_plus_compat :
  real -> real -> real -> real -> real_le -> real_le -> real_le

val real_le_mult_compat :
  real -> real -> real -> real_lt -> real_le -> real_le

val real_lt_zero_one : real_lt

val real_mult_div : real -> real -> real_lt -> real_eq

val real_inv_one_local : real_eq

val real_distrib_r_local : real -> real -> real -> real_eq

val b4_const_eq : q -> q -> real_eq

val b4_const_plus_one : q -> real_eq

val b4_lift_succ : nat -> real_eq

val sf_real_plus_zero_l : real -> real_eq

val real_lt_le_bridge : real -> real -> real_lt -> real_le

val real_eq_le_bridge : real -> real -> real_eq -> real_le

module BudgetReal :
 sig
  val real_pow : real -> nat -> real

  val real_pow_eq_compat : real -> real -> nat -> real_eq -> real_eq

  val cwe_real_pow_pos : real -> nat -> real_lt -> real_lt

  val real_const_zero_thm : real_eq

  val real_mult_one_l : real -> real_eq

  val real_mult_zero_l : real -> real_eq

  val real_nat_mult_succ : nat -> real -> real_eq

  val real_pow_inv_pair : real -> real_lt -> nat -> real_eq

  val cwe_real_le_one_plus : real -> real_le -> real_le

  val real_lt_plus_one : real -> real_lt

  val real_nat_mult_nonneg : nat -> real -> real_lt -> real_le

  val bernoulli_pow : real -> real_lt -> nat -> real_le

  val r_arch_pow_real :
    real -> real_lt -> real_lt -> real -> real_lt -> real -> real_lt -> (nat,
    real_lt) sigT

  val real_pow_add_thm : real -> nat -> nat -> real_eq

  val real_pow_le_one : real -> real_lt -> real_le -> nat -> real_le

  val real_pow_anti_mono : real -> real_lt -> real_le -> nat -> nat -> real_le
 end

val one_minus_delta_pos_real : real -> real_lt -> real_lt

val one_minus_delta_lt_one_real : real -> real_lt -> real_lt

val r_arch_pow_attn_real :
  real -> real_lt -> real_lt -> real -> real_lt -> real -> real_lt -> (nat,
  real_lt) sigT

val tv_iter_decay_real :
  real -> real_lt -> real_lt -> (nat -> real) -> (nat -> real_le) -> nat ->
  real_le

val attention_iterate_converges_real :
  real -> real_lt -> real_lt -> (nat -> real) -> (nat -> real_le) -> real ->
  real_lt -> real_lt -> (nat, nat -> __ -> real_lt) sigT
