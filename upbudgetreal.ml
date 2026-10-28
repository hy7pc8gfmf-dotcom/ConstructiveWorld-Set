
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type ('a, 'p) sigT =
| ExistT of 'a * 'p

(** val projT1 : ('a1, 'a2) sigT -> 'a1 **)

let projT1 = function
| ExistT (a, _) -> a

(** val projT2 : ('a1, 'a2) sigT -> 'a2 **)

let projT2 = function
| ExistT (_, h) -> h

type sumbool =
| Left
| Right

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val max : nat -> nat -> nat **)

let rec max n m =
  match n with
  | O -> m
  | S n' -> (match m with
             | O -> n
             | S m' -> S (max n' m'))

(** val min : nat -> nat -> nat **)

let rec min n m =
  match n with
  | O -> O
  | S n' -> (match m with
             | O -> O
             | S m' -> S (min n' m'))

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n m =
    match n with
    | O -> m
    | S n' -> (match m with
               | O -> n
               | S m' -> S (max n' m'))
 end

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x
 end

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> sumbool **)

let z_lt_le_dec =
  z_lt_ge_dec

type q = { qnum : z; qden : positive }

(** val qcompare : q -> q -> comparison **)

let qcompare p q0 =
  Z.compare (Z.mul p.qnum (Zpos q0.qden)) (Z.mul q0.qnum (Zpos p.qden))

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qdiv : q -> q -> q **)

let qdiv x y =
  qmult x (qinv y)

(** val qlt_le_dec : q -> q -> sumbool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q0 =
  let { qnum = qnum0; qden = _ } = q0 in
  (match qnum0 with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

type 'a id =
| Id_refl

type ('a, 'b) and0 = ('a, 'b) prod

type ('a, 'b) or0 = ('a, 'b) sum

type 'a not = 'a -> empty_set

type natLe = bool id

(** val natLe_lift : nat -> nat -> natLe **)

let natLe_lift n m =
  let b = Nat.leb n m in
  (match b with
   | True -> Id_refl
   | False -> assert false (* absurd case *))

type qseq = nat -> q

(** val qlt_bool : q -> q -> bool **)

let qlt_bool x y =
  match qcompare x y with
  | Lt -> True
  | _ -> False

type qltT = bool id

(** val qlt_to_QltT : q -> q -> qltT **)

let qlt_to_QltT x y =
  let c = qcompare x y in
  (match c with
   | Lt -> Id_refl
   | _ -> assert false (* absurd case *))

type qleT' = bool id

(** val qle_to_QleT' : q -> q -> qleT' **)

let qle_to_QleT' x y =
  let c = Z.compare (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))
  in
  (match c with
   | Gt -> assert false (* absurd case *)
   | _ -> Id_refl)

type qeqT = bool id

(** val qeq_imp_qeqT : q -> q -> qeqT **)

let qeq_imp_qeqT a b =
  let c = qcompare a b in
  (match c with
   | Eq -> Id_refl
   | _ -> assert false (* absurd case *))

(** val qeq_imp_qle : q -> q -> qeqT -> qleT' **)

let qeq_imp_qle a b _ =
  qle_to_QleT' a b

(** val qltT_0_1 : qltT **)

let qltT_0_1 =
  Id_refl

(** val qltT_0_2 : qltT **)

let qltT_0_2 =
  Id_refl

(** val qltT_0_3 : qltT **)

let qltT_0_3 =
  Id_refl

(** val qleT'_refl : q -> qleT' **)

let qleT'_refl x =
  let c = Z.compare (Z.mul x.qnum (Zpos x.qden)) (Z.mul x.qnum (Zpos x.qden))
  in
  (match c with
   | Gt -> assert false (* absurd case *)
   | _ -> Id_refl)

(** val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_trans x _ z0 _ _ =
  qle_to_QleT' x z0

(** val qltT_leT' : q -> q -> qltT -> qleT' **)

let qltT_leT' x y _ =
  qle_to_QleT' x y

(** val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_ltT_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_leT'_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qleT'_plus_compat : q -> q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_plus_compat a b c d _ _ =
  qle_to_QleT' (qplus a c) (qplus b d)

(** val qleT'_plus_nonneg_rT : q -> q -> qleT' -> qleT' **)

let qleT'_plus_nonneg_rT x y hy =
  qleT'_trans x (qplus x { qnum = Z0; qden = XH }) (qplus x y)
    (qeq_imp_qle x (qplus x { qnum = Z0; qden = XH })
      (qeq_imp_qeqT x (qplus x { qnum = Z0; qden = XH })))
    (qleT'_plus_compat x x { qnum = Z0; qden = XH } y (qleT'_refl x) hy)

(** val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qltT_plus_leT'_ltT : q -> q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_plus_leT'_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_plus_ltT_ltT : q -> q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_plus_ltT_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

(** val qleT'_mult_compat_l : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_mult_compat_l x y z0 _ _ =
  qle_to_QleT' (qmult z0 x) (qmult z0 y)

(** val qleT'_mult_ltT_compat :
    q -> q -> q -> q -> qltT -> qleT' -> qleT' -> qltT -> qltT **)

let qleT'_mult_ltT_compat a b c d _ _ _ _ =
  qlt_to_QltT (qmult a c) (qmult b d)

(** val qmult_ltT_0_compat : q -> q -> qltT -> qltT -> qltT **)

let qmult_ltT_0_compat a b _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qmult a b)

(** val qeq_leT' : q -> q -> qeqT -> qleT' **)

let qeq_leT' =
  qeq_imp_qle

(** val qabs_nonnegT : q -> qleT' **)

let qabs_nonnegT x =
  qle_to_QleT' { qnum = Z0; qden = XH } (qabs x)

(** val qltT_plus_pos_r : q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_pos_r x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qplus x y)

(** val qltT_div_pos : q -> q -> qltT -> qltT -> qltT **)

let qltT_div_pos x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x y)

(** val qltT_eq_compat_l : q -> q -> q -> qeqT -> qltT -> qltT **)

let qltT_eq_compat_l _ a' b _ _ =
  qlt_to_QltT a' b

(** val qltT_eq_compat_r : q -> q -> q -> qeqT -> qltT -> qltT **)

let qltT_eq_compat_r a _ b _ _ =
  qlt_to_QltT b a

(** val qltT_mult_ltT_compat_r : q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_mult_ltT_compat_r a b c _ _ =
  qlt_to_QltT (qmult a c) (qmult b c)

type cauchy = q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT

type real = (qseq, cauchy) sigT

type real_eq = q -> qltT -> (nat, nat -> natLe -> qltT) sigT

(** val real_plus : real -> real -> real **)

let real_plus x y =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  ExistT ((fun n -> qplus (x0 n) (x1 n)), (fun eps _ ->
  let s =
    c (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s in
  let s0 =
    c0 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x3, _) = s0 in
  ExistT ((max x2 x3), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qplus (x0 m) (x1 m)) (qplus (x0 n) (x1 n)))) eps))))

(** val real_opp : real -> real **)

let real_opp = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qopp (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qopp (x0 m)) (qopp (x0 n)))) eps))))

(** val real_zero : real **)

let real_zero =
  ExistT ((fun _ -> { qnum = Z0; qden = XH }), (fun _ heps -> ExistT (O,
    (fun _ _ _ _ -> heps))))

type real_lt = (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT

type real_le = (real_lt, real_eq) or0

(** val real_lt_trans :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_trans x _ z0 hxy hyz =
  let ExistT (x0, a) = hxy in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let ExistT (x2, a0) = hyz in
  let Pair (_, s0) = a0 in
  let ExistT (x3, _) = s0 in
  ExistT ((qplus x0 x2), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qplus x0 x2)), (ExistT
  ((max x1 x3), (fun n _ ->
  qlt_to_QltT (qplus x0 x2) (qminus (projT1 z0 n) (projT1 x n))))))))

(** val sum_abs_prefix : qseq -> nat -> q **)

let rec sum_abs_prefix u = function
| O -> { qnum = Z0; qden = XH }
| S n' -> qplus (sum_abs_prefix u n') (qabs (u n'))

(** val cauchy_bounded : qseq -> cauchy -> (q, nat -> qleT') sigT **)

let cauchy_bounded u hu =
  let s = hu { qnum = (Zpos XH); qden = XH } Id_refl in
  let ExistT (x, _) = s in
  ExistT
  ((qplus (qplus (sum_abs_prefix u x) (qabs (u x))) { qnum = (Zpos XH);
     qden = XH }),
  (fun n ->
  qle_to_QleT' (qabs (u n))
    (qplus (qplus (sum_abs_prefix u x) (qabs (u x))) { qnum = (Zpos XH);
      qden = XH })))

(** val qeq_le : q -> q -> qeqT -> qleT' **)

let qeq_le =
  qeq_imp_qle

(** val real_norm_bounded : real -> (q, (qltT, nat -> qleT') and0) sigT **)

let real_norm_bounded = function
| ExistT (x0, c) ->
  let s = cauchy_bounded x0 c in
  let ExistT (x1, _) = s in
  ExistT ((qplus (qabs x1) { qnum = (Zpos XH); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qplus (qabs x1) { qnum = (Zpos XH); qden = XH })),
  (fun k ->
  qle_to_QleT' (qabs (projT1 (ExistT (x0, c)) k))
    (qplus (qabs x1) { qnum = (Zpos XH); qden = XH })))))

(** val real_mult : real -> real -> real **)

let real_mult x y =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  ExistT ((fun n -> qmult (x0 n) (x1 n)), (fun eps _ ->
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, a) = s in
  let Pair (_, q0) = a in
  let s0 = real_norm_bounded (ExistT (x1, c0)) in
  let ExistT (x3, a0) = s0 in
  let Pair (_, q1) = a0 in
  let mupos = qplus { qnum = (Zpos XH); qden = XH } (qabs x2) in
  let mvpos = qplus { qnum = (Zpos XH); qden = XH } (qabs x3) in
  let s1 =
    c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
  in
  let ExistT (x4, q2) = s1 in
  let s2 =
    c0 (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
  in
  let ExistT (x5, q3) = s2 in
  ExistT ((max x4 x5), (fun m n _ _ ->
  let hN1' = q2 m n in
  let hN2' = q3 m n in
  let htriT =
    qle_to_QleT' (qabs (qminus (qmult (x0 m) (x1 m)) (qmult (x0 n) (x1 n))))
      (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
  in
  let hMu_boundT =
    qleT'_trans (qabs (x0 m)) x2 mupos (q0 m) (qle_to_QleT' x2 mupos)
  in
  let hMv_boundT =
    qleT'_trans (qabs (x1 n)) x3 mvpos (q1 n) (qle_to_QleT' x3 mvpos)
  in
  let ht1T =
    qleT'_mult_ltT_compat (qabs (x0 m)) mupos (qabs (qminus (x1 m) (x1 n)))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
      (qlt_to_QltT { qnum = Z0; qden = XH } mupos)
      (qabs_nonnegT (qminus (x1 m) (x1 n))) hMu_boundT
      (hN2' (natLe_lift x5 m) (natLe_lift x5 n))
  in
  let ht2T =
    qleT'_mult_ltT_compat (qabs (x1 n)) mvpos (qabs (qminus (x0 m) (x0 n)))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
      (qlt_to_QltT { qnum = Z0; qden = XH } mvpos)
      (qabs_nonnegT (qminus (x0 m) (x0 n))) hMv_boundT
      (hN1' (natLe_lift x4 m) (natLe_lift x4 n))
  in
  qleT'_ltT_ltT (qabs (qminus (qmult (x0 m) (x1 m)) (qmult (x0 n) (x1 n))))
    (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
      (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
    eps htriT
    (qltT_leT'_ltT
      (qplus (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n)))))
      (qplus
        (qmult mupos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
        (qmult mvpos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
      eps
      (qltT_plus_ltT (qmult (qabs (x0 m)) (qabs (qminus (x1 m) (x1 n))))
        (qmult mupos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
        (qmult (qabs (x1 n)) (qabs (qminus (x0 m) (x0 n))))
        (qmult mvpos
          (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
        ht1T ht2T)
      (qeq_leT'
        (qplus
          (qmult mupos
            (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
          (qmult mvpos
            (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
        eps
        (qeq_imp_qeqT
          (qplus
            (qmult mupos
              (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
            (qmult mvpos
              (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))))
          eps)))))))

(** val real_const : q -> real **)

let real_const c =
  ExistT ((fun _ -> c), (fun _ _ -> ExistT (O, (fun _ _ _ _ -> Id_refl))))

(** val real_eq_refl : real -> real_eq **)

let real_eq_refl _ _ _ =
  ExistT (O, (fun _ _ -> Id_refl))

(** val real_eq_sym : real -> real -> real_eq -> real_eq **)

let real_eq_sym _ _ hxy =
  hxy

(** val real_eq_trans :
    real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_eq_trans x _ z0 hxy hyz eps _ =
  let s =
    hxy (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x0, _) = s in
  let s0 =
    hyz (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x1, _) = s0 in
  ExistT ((max x0 x1), (fun n _ ->
  qlt_to_QltT (qabs (qminus (projT1 x n) (projT1 z0 n))) eps))

(** val real_one : real **)

let real_one =
  ExistT ((fun _ -> { qnum = (Zpos XH); qden = XH }), (fun _ _ -> ExistT (O,
    (fun _ _ _ _ -> Id_refl))))

(** val real_eq_of_zero_diff : real -> real -> (nat -> qeqT) -> real_eq **)

let real_eq_of_zero_diff _ _ _ _ _ =
  ExistT (O, (fun _ _ -> Id_refl))

(** val real_plus_comm : real -> real -> real_eq **)

let real_plus_comm x y =
  real_eq_of_zero_diff (real_plus x y) (real_plus y x) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_plus x y) n) (projT1 (real_plus y x) n)) { qnum =
      Z0; qden = XH })

(** val real_plus_assoc : real -> real -> real -> real_eq **)

let real_plus_assoc x y z0 =
  real_eq_of_zero_diff (real_plus x (real_plus y z0))
    (real_plus (real_plus x y) z0) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_plus x (real_plus y z0)) n)
        (projT1 (real_plus (real_plus x y) z0) n))
      { qnum = Z0; qden = XH })

(** val real_plus_zero : real -> real_eq **)

let real_plus_zero x =
  real_eq_of_zero_diff (real_plus x real_zero) x (fun n ->
    qeq_imp_qeqT (qminus (projT1 (real_plus x real_zero) n) (projT1 x n))
      { qnum = Z0; qden = XH })

(** val real_plus_opp : real -> real_eq **)

let real_plus_opp x =
  real_eq_of_zero_diff (real_plus x (real_opp x)) real_zero (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_plus x (real_opp x)) n) (projT1 real_zero n))
      { qnum = Z0; qden = XH })

(** val real_mult_comm : real -> real -> real_eq **)

let real_mult_comm x y =
  real_eq_of_zero_diff (real_mult x y) (real_mult y x) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_mult x y) n) (projT1 (real_mult y x) n)) { qnum =
      Z0; qden = XH })

(** val real_mult_assoc : real -> real -> real -> real_eq **)

let real_mult_assoc x y z0 =
  real_eq_of_zero_diff (real_mult x (real_mult y z0))
    (real_mult (real_mult x y) z0) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_mult x (real_mult y z0)) n)
        (projT1 (real_mult (real_mult x y) z0) n))
      { qnum = Z0; qden = XH })

(** val real_mult_one : real -> real_eq **)

let real_mult_one x =
  real_eq_of_zero_diff (real_mult x real_one) x (fun n ->
    qeq_imp_qeqT (qminus (projT1 (real_mult x real_one) n) (projT1 x n))
      { qnum = Z0; qden = XH })

(** val real_mult_zero : real -> real_eq **)

let real_mult_zero x =
  real_eq_of_zero_diff (real_mult x real_zero) real_zero (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_mult x real_zero) n) (projT1 real_zero n))
      { qnum = Z0; qden = XH })

(** val real_distrib : real -> real -> real -> real_eq **)

let real_distrib x y z0 =
  real_eq_of_zero_diff (real_mult x (real_plus y z0))
    (real_plus (real_mult x y) (real_mult x z0)) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_mult x (real_plus y z0)) n)
        (projT1 (real_plus (real_mult x y) (real_mult x z0)) n))
      { qnum = Z0; qden = XH })

(** val real_le_refl : real -> real_le **)

let real_le_refl x =
  Inr (real_eq_refl x)

(** val real_lt_eq_lt :
    real -> real -> real -> real_lt -> real_eq -> real_lt **)

let real_lt_eq_lt x _ z0 hlt hyz =
  let ExistT (x0, a) = hlt in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 =
    hyz (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s0 in
  ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((max x1 x2), (fun n _ ->
  qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 z0 n) (projT1 x n))))))))

(** val real_eq_lt_lt :
    real -> real -> real -> real_eq -> real_lt -> real_lt **)

let real_eq_lt_lt x _ z0 hxy = function
| ExistT (x0, a) ->
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 =
    hxy (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }))
  in
  let ExistT (x2, _) = s0 in
  ExistT ((qdiv x0 { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((max x1 x2), (fun n _ ->
  qlt_to_QltT (qdiv x0 { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 z0 n) (projT1 x n))))))))

(** val real_le_trans :
    real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_trans x y z0 hxy hyz =
  match hxy with
  | Inl hlt ->
    (match hyz with
     | Inl hlt' -> Inl (real_lt_trans x y z0 hlt hlt')
     | Inr heq' -> Inl (real_lt_eq_lt x y z0 hlt heq'))
  | Inr heq ->
    (match hyz with
     | Inl hlt' -> Inl (real_eq_lt_lt x y z0 heq hlt')
     | Inr heq' -> Inr (real_eq_trans x y z0 heq heq'))

(** val real_lt_le_trans :
    real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_le_trans x y z0 hlt = function
| Inl hlt' -> real_lt_trans x y z0 hlt hlt'
| Inr heq' -> real_lt_eq_lt x y z0 hlt heq'

(** val real_le_lt_trans :
    real -> real -> real -> real_le -> real_lt -> real_lt **)

let real_le_lt_trans x y z0 hle hlt =
  match hle with
  | Inl hlt' -> real_lt_trans x y z0 hlt' hlt
  | Inr heq -> real_eq_lt_lt x y z0 heq hlt

(** val real_lt_le_iff : real -> real -> (real_lt, real id) or0 -> real_le **)

let real_lt_le_iff x _ = function
| Inl r -> Inl r
| Inr _ -> Inr (real_eq_refl x)

(** val real_lt_plus_compat :
    real -> real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_lt_plus_compat a b c d hab hcd =
  let ExistT (x, a0) = hab in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hcd in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qplus x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qplus x x1)), (ExistT ((max x0 x2),
  (fun n _ ->
  qlt_to_QltT (qplus x x1)
    (qminus (projT1 (real_plus b d) n) (projT1 (real_plus a c) n))))))))

(** val q_pow : q -> nat -> q **)

let rec q_pow x = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult x (q_pow x m)

(** val q_fact : nat -> q **)

let rec q_fact = function
| O -> { qnum = (Zpos XH); qden = XH }
| S m -> qmult { qnum = (Z.of_nat (S m)); qden = XH } (q_fact m)

(** val exp_partial : nat -> q -> q **)

let rec exp_partial n x =
  match n with
  | O -> { qnum = (Zpos XH); qden = XH }
  | S m -> qplus (exp_partial m x) (qdiv (q_pow x (S m)) (q_fact (S m)))

(** val q_arch_geom : q -> (nat, nat -> natLe -> qleT') sigT **)

let q_arch_geom a =
  let s =
    qarchimedean
      (qmult
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH })
        a)
  in
  ExistT ((Coq_Pos.to_nat s), (fun t _ ->
  qle_to_QleT'
    (qmult
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
      a)
    { qnum = (Z.of_nat (add t (S O))); qden = XH }))

(** val arch_decay : q -> q -> qleT' -> qltT -> (nat, qltT) sigT **)

let arch_decay c eps _ _ =
  let s = qarchimedean (qdiv c eps) in
  ExistT ((Coq_Pos.to_nat s),
  (qlt_to_QltT
    (qmult c
      (q_pow
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })
        (S (Coq_Pos.to_nat s))))
    eps))

(** val q_pow_fact2_nonneg : q -> nat -> qleT' -> qleT' **)

let q_pow_fact2_nonneg a m _ =
  qle_to_QleT' { qnum = Z0; qden = XH }
    (qmult (qdiv (q_pow a m) (q_fact m))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH }))

(** val exp_partial_cauchy :
    q -> q -> qltT -> (nat, nat -> nat -> natLe -> natLe -> qltT) sigT **)

let exp_partial_cauchy x eps hep =
  let a = qabs x in
  let s = q_arch_geom a in
  let ExistT (x0, _) = s in
  let c =
    qmult (qdiv (q_pow a x0) (q_fact x0))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let hC = q_pow_fact2_nonneg a x0 (qle_to_QleT' { qnum = Z0; qden = XH } a)
  in
  let s0 = arch_decay c eps hC hep in
  let ExistT (x1, _) = s0 in
  ExistT ((add x0 (S x1)), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (exp_partial m x) (exp_partial n x))) eps))

(** val exp_series : nat -> q -> q **)

let rec exp_series n b =
  match n with
  | O -> { qnum = (Zpos XH); qden = XH }
  | S m -> qplus (exp_series m b) (qdiv (q_pow b (S m)) (q_fact (S m)))

(** val exp_partial_cauchy_bounded :
    q -> q -> qleT' -> qltT -> (nat, nat -> nat -> natLe -> natLe -> q ->
    qleT' -> qltT) sigT **)

let exp_partial_cauchy_bounded b eps _ hep =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let c =
    qmult (qdiv (q_pow b x) (q_fact x))
      (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden = XH })
  in
  let s0 = arch_decay c eps (qle_to_QleT' { qnum = Z0; qden = XH } c) hep in
  let ExistT (x0, _) = s0 in
  ExistT ((add x (S x0)), (fun m n _ _ y _ ->
  qlt_to_QltT (qabs (qminus (exp_partial m y) (exp_partial n y))) eps))

(** val exp_series_arch :
    q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT **)

let exp_series_arch b _ =
  let s = q_arch_geom b in
  let ExistT (x, _) = s in
  let c =
    qplus (exp_series x b)
      (qmult (qdiv (q_pow b x) (q_fact x))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
  in
  ExistT (c, (Pair ((qle_to_QleT' { qnum = (Zpos XH); qden = XH } c),
  (fun n -> qle_to_QleT' (exp_series n b) c))))

(** val exp_partial_lipschitz :
    q -> q -> q -> nat -> qleT' -> qleT' -> qleT' -> qleT' **)

let exp_partial_lipschitz x y b m _ _ _ =
  qle_to_QleT' (qabs (qminus (exp_partial m x) (exp_partial m y)))
    (qmult (qabs (qminus x y)) (exp_series m b))

(** val cauchy_real_exp : real -> real **)

let cauchy_real_exp = function
| ExistT (x0, c) ->
  ExistT ((fun n -> exp_partial n (x0 n)), (fun eps heps ->
    let s = real_norm_bounded (ExistT (x0, c)) in
    let ExistT (x1, a) = s in
    let Pair (q0, q1) = a in
    let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
    let ExistT (x2, a0) = s0 in
    let Pair (q2, q3) = a0 in
    let hCposT =
      qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH }
        x2 qltT_0_1 q2
    in
    let s1 =
      c (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
        (qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)
          heps
          (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x2
            qltT_0_2 hCposT))
    in
    let ExistT (x3, q4) = s1 in
    let heps2 =
      qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2
    in
    let s2 =
      exp_partial_cauchy_bounded x1
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
        (qltT_leT' { qnum = Z0; qden = XH } x1 q0) heps2
    in
    let ExistT (x4, q5) = s2 in
    ExistT ((Nat.max x3 x4), (fun m n _ _ ->
    qltT_eq_compat_l
      (qabs
        (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
          (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
      (qabs (qminus (exp_partial m (x0 m)) (exp_partial n (x0 n)))) eps
      (qeq_imp_qeqT
        (qabs
          (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
            (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
        (qabs (qminus (exp_partial m (x0 m)) (exp_partial n (x0 n)))))
      (let htriT =
         qle_to_QleT'
           (qabs
             (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
               (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
           (qplus
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
       in
       let ht1T =
         qleT'_trans
           (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
           (qmult (qabs (qminus (x0 m) (x0 n))) (exp_series m x1))
           (qmult (qabs (qminus (x0 m) (x0 n))) x2)
           (exp_partial_lipschitz (x0 m) (x0 n) x1 m
             (qltT_leT' { qnum = Z0; qden = XH } x1 q0) (q1 m) (q1 n))
           (qleT'_mult_compat_l (exp_series m x1) x2
             (qabs (qminus (x0 m) (x0 n)))
             (qabs_nonnegT (qminus (x0 m) (x0 n))) (q3 m))
       in
       let ht2T = q5 m n (natLe_lift x4 m) (natLe_lift x4 n) (x0 n) (q1 n) in
       let ht3T =
         qltT_leT'_ltT (qmult (qabs (qminus (x0 m) (x0 n))) x2)
           (qmult (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
             x2)
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
           (qltT_mult_ltT_compat_r (qabs (qminus (x0 m) (x0 n)))
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)) x2
             hCposT (q4 m n (natLe_lift x3 m) (natLe_lift x3 n)))
           (qeq_leT'
             (qmult
               (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)) x2)
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qeq_imp_qeqT
               (qmult
                 (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
                 x2)
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })))
       in
       qleT'_ltT_ltT
         (qabs
           (qplus (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n)))
             (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
         (qplus (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
           (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
         eps htriT
         (qltT_leT'_ltT
           (qplus
             (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
             (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
           (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
           eps
           (qltT_leT'_ltT
             (qplus
               (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
               (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n)))))
             (qplus (qmult (qabs (qminus (x0 m) (x0 n))) x2)
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             (qleT'_plus_ltT_ltT
               (qabs (qminus (exp_partial m (x0 m)) (exp_partial m (x0 n))))
               (qmult (qabs (qminus (x0 m) (x0 n))) x2)
               (qabs (qminus (exp_partial m (x0 n)) (exp_partial n (x0 n))))
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T ht2T)
             (qltT_leT'
               (qplus (qmult (qabs (qminus (x0 m) (x0 n))) x2)
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               (qltT_plus_leT'_ltT (qmult (qabs (qminus (x0 m) (x0 n))) x2)
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht3T
                 (qleT'_refl (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })))))
           (qeq_leT'
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             eps
             (qeq_imp_qeqT
               (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               eps))))))))

(** val cauchy_real_exp_zero : real_eq **)

let cauchy_real_exp_zero eps _ =
  ExistT (O, (fun n _ ->
    qlt_to_QltT { qnum =
      (Z.abs
        (Z.add
          (Z.mul (exp_partial n { qnum = Z0; qden = XH }).qnum (Zpos XH))
          (Zneg (exp_partial n { qnum = Z0; qden = XH }).qden)));
      qden = (Coq_Pos.mul (exp_partial n { qnum = Z0; qden = XH }).qden XH) }
      eps))

(** val sum_upto : nat -> (nat -> q) -> q **)

let rec sum_upto n f =
  match n with
  | O -> { qnum = Z0; qden = XH }
  | S n' -> qplus (sum_upto n' f) (f n')

(** val exp_partial_tail_small :
    q -> q -> qleT' -> qleT' -> (nat, nat -> natLe -> qltT) sigT **)

let exp_partial_tail_small m c hM _ =
  let s = q_arch_geom m in
  let ExistT (x, _) = s in
  let s0 =
    arch_decay
      (qmult (qdiv (q_pow m x) (q_fact x))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qdiv { qnum = (Zpos XH); qden = XH } c) (q_pow_fact2_nonneg m x hM)
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv { qnum = (Zpos XH); qden = XH } c))
  in
  let ExistT (x0, _) = s0 in
  ExistT ((add x (S x0)), (fun m0 _ ->
  qlt_to_QltT
    (qdiv (q_pow m (add (mul (S (S O)) m0) (S O)))
      (q_fact (add (mul (S (S O)) m0) (S O))))
    (qdiv { qnum = (Zpos XH); qden = XH }
      (qmult { qnum = (Zpos (XO XH)); qden = XH } c))))

(** val cauchy_real_exp_pos : real -> real_lt **)

let cauchy_real_exp_pos = function
| ExistT (x0, c) ->
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x1, a) = s in
  let Pair (q0, _) = a in
  let s0 = exp_series_arch x1 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) in
  let ExistT (x2, a0) = s0 in
  let Pair (q1, _) = a0 in
  let hCposT =
    qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } x2
      qltT_0_1 q1
  in
  let s1 =
    exp_partial_tail_small x1 x2 (qltT_leT' { qnum = Z0; qden = XH } x1 q0) q1
  in
  let ExistT (x3, _) = s1 in
  ExistT
  ((qdiv { qnum = (Zpos XH); qden = XH }
     (qmult { qnum = (Zpos (XO XH)); qden = XH } x2)),
  (Pair
  ((qltT_div_pos { qnum = (Zpos XH); qden = XH }
     (qmult { qnum = (Zpos (XO XH)); qden = XH } x2) qltT_0_1
     (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x2 qltT_0_2
       hCposT)),
  (ExistT ((add (mul (S (S O)) x3) (S O)), (fun n _ ->
  qltT_eq_compat_r (qminus (exp_partial n (x0 n)) { qnum = Z0; qden = XH })
    (exp_partial n (x0 n))
    (qdiv { qnum = (Zpos XH); qden = XH }
      (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
    (qeq_imp_qeqT (qminus (exp_partial n (x0 n)) { qnum = Z0; qden = XH })
      (exp_partial n (x0 n)))
    (qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH }
        (qmult { qnum = (Zpos (XO XH)); qden = XH } x2))
      (exp_partial n (x0 n)))))))))

(** val real_abs : real -> real **)

let real_abs = function
| ExistT (x0, c) ->
  ExistT ((fun n -> qabs (x0 n)), (fun eps heps ->
    let s = c eps heps in
    let ExistT (x1, _) = s in
    ExistT (x1, (fun m n _ _ ->
    qlt_to_QltT (qabs (qminus (qabs (x0 m)) (qabs (x0 n)))) eps))))

(** val real_inv_pos : real -> real_lt -> real **)

let real_inv_pos x hx =
  let ExistT (x0, c) = x in
  let ExistT (x1, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x2, _) = s in
  ExistT ((fun n ->
  match Nat.leb x2 n with
  | True -> qinv (x0 n)
  | False -> qinv (x0 x2)), (fun eps _ ->
  let delta = qmult eps (qmult x1 x1) in
  let hdlt = qlt_to_QltT { qnum = Z0; qden = XH } (qmult eps (qmult x1 x1)) in
  let s0 = c delta hdlt in
  let ExistT (x3, _) = s0 in
  ExistT ((Nat.max x2 x3), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (qinv (x0 m)) (qinv (x0 n)))) eps))))

(** val real_inv_pos_correct : real -> real_lt -> real_eq **)

let real_inv_pos_correct x hx eps _ =
  let ExistT (x0, _) = x in
  let ExistT (_, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x1, (fun n _ ->
  let b = Nat.leb x1 n in
  (match b with
   | True ->
     qlt_to_QltT
       (qabs
         (qminus (qmult (x0 n) (qinv (x0 n))) { qnum = (Zpos XH); qden = XH }))
       eps
   | False -> assert false (* absurd case *))))

(** val real_inv_pos_pos : real -> real_lt -> real_lt **)

let real_inv_pos_pos x hx =
  let ExistT (x0, c) = x in
  let ExistT (_, a) = hx in
  let Pair (_, s) = a in
  let ExistT (x1, _) = s in
  let s0 = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, _) = s0 in
  ExistT ((qinv (qplus x2 { qnum = (Zpos XH); qden = XH })), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qinv (qplus x2 { qnum = (Zpos XH); qden = XH }))),
  (ExistT (x1, (fun n _ ->
  let b = Nat.leb x1 n in
  (match b with
   | True ->
     qlt_to_QltT (qinv (qplus x2 { qnum = (Zpos XH); qden = XH }))
       (qminus (qinv (x0 n)) { qnum = Z0; qden = XH })
   | False -> assert false (* absurd case *))))))))

module RealSetoid =
 struct
  (** val real_eq_le : real -> real -> real_eq -> real_le **)

  let real_eq_le _ _ hab =
    Inr hab

  (** val real_lt_le_iff_req :
      real -> real -> (real_lt, real_eq) or0 -> real_le **)

  let real_lt_le_iff_req a b = function
  | Inl r -> real_lt_le_iff a b (Inl r)
  | Inr r -> real_eq_le a b r

  (** val real_eq_plus_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_plus_compat a b c d hac hbd eps _ =
    let hhalf0 =
      qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
    in
    let s = hac (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
    let ExistT (x, _) = s in
    let s0 = hbd (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hhalf0 in
    let ExistT (x0, _) = s0 in
    ExistT ((Nat.max x x0), (fun k _ ->
    qlt_to_QltT
      (qabs (qminus (projT1 (real_plus a b) k) (projT1 (real_plus c d) k)))
      eps))

  (** val real_eq_mult_compat :
      real -> real -> real -> real -> real_eq -> real_eq -> real_eq **)

  let real_eq_mult_compat a b c d hac hbd eps heps =
    let s = real_norm_bounded a in
    let ExistT (x, a0) = s in
    let Pair (_, q0) = a0 in
    let s0 = real_norm_bounded d in
    let ExistT (x0, a1) = s0 in
    let Pair (_, q1) = a1 in
    let mupos = qplus { qnum = (Zpos XH); qden = XH } (qabs x) in
    let mvpos = qplus { qnum = (Zpos XH); qden = XH } (qabs x0) in
    let muposT = qlt_to_QltT { qnum = Z0; qden = XH } mupos in
    let mvposT = qlt_to_QltT { qnum = Z0; qden = XH } mvpos in
    let hepsB =
      qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)
        heps
        (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } mupos
          qltT_0_2 muposT)
    in
    let hepsA =
      qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)
        heps
        (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } mvpos
          qltT_0_2 mvposT)
    in
    let s1 =
      hbd (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)) hepsB
    in
    let ExistT (x1, q2) = s1 in
    let s2 =
      hac (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)) hepsA
    in
    let ExistT (x2, q3) = s2 in
    ExistT ((Nat.max x1 x2), (fun k _ ->
    qltT_eq_compat_l
      (qabs
        (qminus (qmult (projT1 a k) (projT1 b k))
          (qmult (projT1 c k) (projT1 d k))))
      (qabs (qminus (projT1 (real_mult a b) k) (projT1 (real_mult c d) k)))
      eps
      (qeq_imp_qeqT
        (qabs
          (qminus (qmult (projT1 a k) (projT1 b k))
            (qmult (projT1 c k) (projT1 d k))))
        (qabs (qminus (projT1 (real_mult a b) k) (projT1 (real_mult c d) k))))
      (let hbdT =
         qle_to_QleT'
           (qabs
             (qminus (qmult (projT1 a k) (projT1 b k))
               (qmult (projT1 c k) (projT1 d k))))
           (qplus
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k)))))
       in
       let hMa_boundT =
         qleT'_trans (qabs (projT1 a k)) x mupos (q0 k) (qle_to_QleT' x mupos)
       in
       let hMd_boundT =
         qleT'_trans (qabs (projT1 d k)) x0 mvpos (q1 k)
           (qle_to_QleT' x0 mvpos)
       in
       let ht1T =
         qleT'_mult_ltT_compat (qabs (projT1 a k)) mupos
           (qabs (qminus (projT1 b k) (projT1 d k)))
           (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos))
           muposT (qabs_nonnegT (qminus (projT1 b k) (projT1 d k)))
           hMa_boundT (q2 k (natLe_lift x1 k))
       in
       let ht2T =
         qleT'_mult_ltT_compat (qabs (projT1 d k)) mvpos
           (qabs (qminus (projT1 a k) (projT1 c k)))
           (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos))
           mvposT (qabs_nonnegT (qminus (projT1 a k) (projT1 c k)))
           hMd_boundT (q3 k (natLe_lift x2 k))
       in
       let ht1bT =
         qeq_leT'
           (qmult mupos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
           (qeq_imp_qeqT
             (qmult mupos
               (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
       in
       let ht2bT =
         qeq_leT'
           (qmult mvpos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
           (qeq_imp_qeqT
             (qmult mvpos
               (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
       in
       let ht1T' =
         qltT_leT'_ltT
           (qmult (qabs (projT1 a k))
             (qabs (qminus (projT1 b k) (projT1 d k))))
           (qmult mupos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mupos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T ht1bT
       in
       let ht2T' =
         qltT_leT'_ltT
           (qmult (qabs (projT1 d k))
             (qabs (qminus (projT1 a k) (projT1 c k))))
           (qmult mvpos
             (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } mvpos)))
           (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht2T ht2bT
       in
       qleT'_ltT_ltT
         (qabs
           (qminus (qmult (projT1 a k) (projT1 b k))
             (qmult (projT1 c k) (projT1 d k))))
         (qplus
           (qmult (qabs (projT1 a k))
             (qabs (qminus (projT1 b k) (projT1 d k))))
           (qmult (qabs (projT1 d k))
             (qabs (qminus (projT1 a k) (projT1 c k)))))
         eps hbdT
         (qltT_leT'_ltT
           (qplus
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k)))))
           (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
           eps
           (qltT_plus_ltT
             (qmult (qabs (projT1 a k))
               (qabs (qminus (projT1 b k) (projT1 d k))))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
             (qmult (qabs (projT1 d k))
               (qabs (qminus (projT1 a k) (projT1 c k))))
             (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) ht1T' ht2T')
           (qeq_leT'
             (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
               (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
             eps
             (qeq_imp_qeqT
               (qplus (qdiv eps { qnum = (Zpos (XO XH)); qden = XH })
                 (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }))
               eps))))))
 end

(** val exp_trunc_arch_seq :
    (nat -> q) -> (nat -> q) -> q -> q -> qleT' -> (nat -> qleT') -> (nat ->
    qleT') -> qltT -> (nat, nat -> natLe -> qltT) sigT **)

let exp_trunc_arch_seq u v b eps hB _ _ _ =
  let s = exp_series_arch b hB in
  let ExistT (x, _) = s in
  let s0 = q_arch_geom b in
  let ExistT (x0, _) = s0 in
  let s1 =
    arch_decay
      (qmult (qdiv (q_pow b x0) (q_fact x0))
        (qplus { qnum = (Zpos XH); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x))
      (q_pow_fact2_nonneg b x0 hB)
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x)))
  in
  let ExistT (x1, _) = s1 in
  ExistT ((add x0 (S x1)), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (sum_upto (S (mul (S (S O)) n)) (fun j ->
          sum_upto (S (sub (mul (S (S O)) n) j)) (fun i ->
            qmult (qdiv (q_pow (u n) j) (q_fact j))
              (qdiv (q_pow (v n) i) (q_fact i)))))
        (sum_upto (S n) (fun j ->
          sum_upto (S n) (fun i ->
            qmult (qdiv (q_pow (u n) j) (q_fact j))
              (qdiv (q_pow (v n) i) (q_fact i)))))))
    eps))

(** val cauchy_real_exp_plus : real -> real -> real_eq **)

let cauchy_real_exp_plus x y eps heps =
  let ExistT (x0, c) = x in
  let ExistT (x1, c0) = y in
  let s = real_norm_bounded (ExistT (x0, c)) in
  let ExistT (x2, a) = s in
  let Pair (q0, q1) = a in
  let s0 = real_norm_bounded (ExistT (x1, c0)) in
  let ExistT (x3, a0) = s0 in
  let Pair (q2, q3) = a0 in
  let m = qplus x2 x3 in
  let hMposT = qltT_plus_pos_r x2 x3 q0 q2 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let huMT = fun n ->
    qleT'_trans (qabs (x0 n)) x2 (qplus x2 x3) (q1 n)
      (qleT'_plus_nonneg_rT x2 x3 (qltT_leT' { qnum = Z0; qden = XH } x3 q2))
  in
  let hvMT = fun n ->
    qleT'_trans (qabs (x1 n)) x3 (qplus x2 x3) (q3 n)
      (qleT'_trans x3 (qplus x3 x2) (qplus x2 x3)
        (qleT'_plus_nonneg_rT x3 x2
          (qltT_leT' { qnum = Z0; qden = XH } x2 q0))
        (qeq_le (qplus x3 x2) (qplus x2 x3)
          (qeq_imp_qeqT (qplus x3 x2) (qplus x2 x3))))
  in
  let heps3T =
    qltT_div_pos eps { qnum = (Zpos (XI XH)); qden = XH } heps qltT_0_3
  in
  let s1 =
    exp_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT heps3T
  in
  let ExistT (x4, _) = s1 in
  let s2 =
    exp_trunc_arch_seq x0 x1 m
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) hMnonnegT huMT hvMT
      heps3T
  in
  let ExistT (x5, _) = s2 in
  ExistT ((Nat.max x4 x5), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1
          (cauchy_real_exp (real_plus (ExistT (x0, c)) (ExistT (x1, c0)))) n)
        (projT1
          (real_mult (cauchy_real_exp (ExistT (x0, c)))
            (cauchy_real_exp (ExistT (x1, c0))))
          n)))
    eps))

(** val cauchy_real_exp_gt_one : real -> real_lt -> real_lt **)

let cauchy_real_exp_gt_one t = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT ((Nat.max x0 (S O)), (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (cauchy_real_exp t) n) (projT1 real_one n))))))))

(** val real_lt_opp_plus : real -> real -> real_lt -> real_lt **)

let real_lt_opp_plus x y = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0
    (qminus (projT1 (real_plus y (real_opp x)) n) (projT1 real_zero n))))))))

(** val real_mult_pos_compat :
    real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_pos_compat a b ha hb =
  let ExistT (x, a0) = ha in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hb in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult a b) n) (projT1 real_zero n))))))))

(** val cauchy_real_exp_minus_one_pos : real -> real_lt -> real_lt **)

let cauchy_real_exp_minus_one_pos t ht =
  let r = cauchy_real_exp_gt_one t ht in
  let ExistT (x, a) = r in
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x
    (qminus (projT1 (real_plus (cauchy_real_exp t) (real_opp real_one)) n)
      (projT1 real_zero n))))))))

(** val cauchy_real_exp_wd : real -> real -> real_eq -> real_eq **)

let cauchy_real_exp_wd a b hab eps heps =
  let s = real_norm_bounded a in
  let ExistT (x, a0) = s in
  let Pair (q0, _) = a0 in
  let s0 = real_norm_bounded b in
  let ExistT (x0, a1) = s0 in
  let Pair (q1, _) = a1 in
  let m = qplus x x0 in
  let hMposT = qltT_plus_pos_r x x0 q0 q1 in
  let hMnonnegT = qltT_leT' { qnum = Z0; qden = XH } m hMposT in
  let s1 = exp_series_arch m hMnonnegT in
  let ExistT (x1, a2) = s1 in
  let Pair (q2, _) = a2 in
  let hCposT =
    qltT_leT'_ltT { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH } x1
      qltT_0_1 q2
  in
  let hepsC =
    qltT_div_pos eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x1) heps
      (qmult_ltT_0_compat { qnum = (Zpos (XO XH)); qden = XH } x1 qltT_0_2
        hCposT)
  in
  let s2 =
    hab (qdiv eps (qmult { qnum = (Zpos (XO XH)); qden = XH } x1)) hepsC
  in
  let ExistT (x2, _) = s2 in
  let heps2T =
    qltT_div_pos eps { qnum = (Zpos (XO XH)); qden = XH } heps qltT_0_2
  in
  let s3 =
    exp_partial_cauchy_bounded m
      (qdiv eps { qnum = (Zpos (XO XH)); qden = XH }) hMnonnegT heps2T
  in
  let ExistT (x3, _) = s3 in
  ExistT ((Nat.max x2 x3), (fun n _ ->
  qlt_to_QltT
    (qabs
      (qminus (projT1 (cauchy_real_exp a) n) (projT1 (cauchy_real_exp b) n)))
    eps))

(** val real_mult_minus_factor : real -> real -> real_eq **)

let real_mult_minus_factor a b =
  real_eq_of_zero_diff (real_plus (real_mult a b) (real_opp a))
    (real_mult a (real_plus b (real_opp real_one))) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_plus (real_mult a b) (real_opp a)) n)
        (projT1 (real_mult a (real_plus b (real_opp real_one))) n))
      { qnum = Z0; qden = XH })

(** val cauchy_real_exp_mono : real -> real -> real_lt -> real_lt **)

let cauchy_real_exp_mono x y hxy =
  let hdiff = real_lt_opp_plus x y hxy in
  let hminus = cauchy_real_exp_minus_one_pos (real_plus y (real_opp x)) hdiff
  in
  let hprod =
    real_mult_pos_compat (cauchy_real_exp x)
      (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
        (real_opp real_one))
      (cauchy_real_exp_pos x) hminus
  in
  let hxyeq =
    real_eq_of_zero_diff y (real_plus x (real_plus y (real_opp x))) (fun n ->
      qeq_imp_qeqT
        (qminus (projT1 y n)
          (projT1 (real_plus x (real_plus y (real_opp x))) n))
        { qnum = Z0; qden = XH })
  in
  let hewd =
    cauchy_real_exp_wd y (real_plus x (real_plus y (real_opp x))) hxyeq
  in
  let heplus = cauchy_real_exp_plus x (real_plus y (real_opp x)) in
  let hmain =
    real_eq_trans (cauchy_real_exp y)
      (cauchy_real_exp (real_plus x (real_plus y (real_opp x))))
      (real_mult (cauchy_real_exp x)
        (cauchy_real_exp (real_plus y (real_opp x))))
      hewd heplus
  in
  let hdiffeq =
    real_eq_trans
      (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
      (real_plus
        (real_mult (cauchy_real_exp x)
          (cauchy_real_exp (real_plus y (real_opp x))))
        (real_opp (cauchy_real_exp x)))
      (real_mult (cauchy_real_exp x)
        (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
          (real_opp real_one)))
      (RealSetoid.real_eq_plus_compat (cauchy_real_exp y)
        (real_opp (cauchy_real_exp x))
        (real_mult (cauchy_real_exp x)
          (cauchy_real_exp (real_plus y (real_opp x))))
        (real_opp (cauchy_real_exp x)) hmain
        (real_eq_refl (real_opp (cauchy_real_exp x))))
      (real_mult_minus_factor (cauchy_real_exp x)
        (cauchy_real_exp (real_plus y (real_opp x))))
  in
  let hposdiff =
    real_lt_eq_lt real_zero
      (real_mult (cauchy_real_exp x)
        (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
          (real_opp real_one)))
      (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x))) hprod
      (real_eq_sym
        (real_plus (cauchy_real_exp y) (real_opp (cauchy_real_exp x)))
        (real_mult (cauchy_real_exp x)
          (real_plus (cauchy_real_exp (real_plus y (real_opp x)))
            (real_opp real_one)))
        hdiffeq)
  in
  let ExistT (x0, a) = hposdiff in
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0
    (qminus (projT1 (cauchy_real_exp y) n) (projT1 (cauchy_real_exp x) n))))))))

(** val real_arch : real -> (nat, (natLe, real_lt) and0) sigT **)

let real_arch b =
  let s = real_norm_bounded b in
  let ExistT (x, _) = s in
  let s0 = q_arch_geom x in
  let ExistT (x0, _) = s0 in
  ExistT ((add x0 (S (S O))), (Pair
  ((natLe_lift (S (S O)) (add x0 (S (S O)))), (ExistT
  ((qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
     { qnum = (Zpos (XO XH)); qden = XH }),
  (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
       { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT (O, (fun k _ ->
  qlt_to_QltT
    (qdiv (qminus { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH } x)
      { qnum = (Zpos (XO XH)); qden = XH })
    (qminus
      (projT1
        (real_const { qnum = (Z.of_nat (add x0 (S (S O)))); qden = XH }) k)
      (projT1 b k))))))))))))

(** val cauchy_real_exp_gt_const : nat -> real_lt **)

let cauchy_real_exp_gt_const n =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT ((S O), (fun n0 _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus
        (projT1
          (cauchy_real_exp (real_const { qnum = (Z.of_nat n); qden = XH }))
          n0)
        (projT1 (real_const { qnum = (Z.of_nat n); qden = XH }) n0))))))))

(** val log_mid_lt_b : q -> q -> qltT -> qltT **)

let log_mid_lt_b a b _ =
  qlt_to_QltT (qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH }) b

(** val log_a_lt_mid : q -> q -> qltT -> qltT **)

let log_a_lt_mid a b _ =
  qlt_to_QltT a (qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH })

(** val real_abs_diff_le_lift : real -> real -> q -> q -> nat -> real_lt **)

let real_abs_diff_le_lift a b m _UU03b3_ _ =
  let hg4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH })
  in
  let s =
    projT2 a (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH }) hg4
  in
  let ExistT (x, _) = s in
  let s0 =
    projT2 b (qdiv _UU03b3_ { qnum = (Zpos (XO (XO XH))); qden = XH }) hg4
  in
  let ExistT (x0, _) = s0 in
  ExistT ((qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH }), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH }
     (qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH })),
  (ExistT ((Nat.max x x0), (fun n _ ->
  qlt_to_QltT (qdiv _UU03b3_ { qnum = (Zpos (XO XH)); qden = XH })
    (qminus (projT1 (real_const (qplus m _UU03b3_)) n)
      (projT1 (real_abs (real_plus a (real_opp b))) n))))))))

(** val real_inv_unique :
    real -> real -> real -> real_eq -> real_eq -> real_eq **)

let real_inv_unique a b c hab hac =
  real_eq_trans b (real_mult b real_one) c
    (real_eq_sym (real_mult b real_one) b (real_mult_one b))
    (real_eq_trans (real_mult b real_one) (real_mult b (real_mult a c)) c
      (RealSetoid.real_eq_mult_compat b real_one b (real_mult a c)
        (real_eq_refl b) (real_eq_sym (real_mult a c) real_one hac))
      (real_eq_trans (real_mult b (real_mult a c))
        (real_mult (real_mult b a) c) c (real_mult_assoc b a c)
        (real_eq_trans (real_mult (real_mult b a) c)
          (real_mult (real_mult a b) c) c
          (RealSetoid.real_eq_mult_compat (real_mult b a) c (real_mult a b) c
            (real_mult_comm b a) (real_eq_refl c))
          (real_eq_trans (real_mult (real_mult a b) c) (real_mult real_one c)
            c
            (RealSetoid.real_eq_mult_compat (real_mult a b) c real_one c hab
              (real_eq_refl c))
            (real_eq_trans (real_mult real_one c) (real_mult c real_one) c
              (real_mult_comm real_one c) (real_mult_one c))))))

(** val exp_neg_recip : real -> real_lt -> real_eq **)

let exp_neg_recip x hx =
  real_inv_unique (cauchy_real_exp x) (cauchy_real_exp (real_opp x))
    (real_inv_pos (cauchy_real_exp x) hx)
    (real_eq_trans
      (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_opp x)))
      (cauchy_real_exp (real_plus x (real_opp x))) real_one
      (real_eq_sym (cauchy_real_exp (real_plus x (real_opp x)))
        (real_mult (cauchy_real_exp x) (cauchy_real_exp (real_opp x)))
        (cauchy_real_exp_plus x (real_opp x)))
      (real_eq_trans (cauchy_real_exp (real_plus x (real_opp x)))
        (cauchy_real_exp real_zero) real_one
        (cauchy_real_exp_wd (real_plus x (real_opp x)) real_zero
          (real_eq_of_zero_diff (real_plus x (real_opp x)) real_zero
            (fun n ->
            qeq_imp_qeqT
              (qminus (projT1 (real_plus x (real_opp x)) n)
                (projT1 real_zero n))
              { qnum = Z0; qden = XH })))
        cauchy_real_exp_zero))
    (real_inv_pos_correct (cauchy_real_exp x) hx)

(** val real_const_pos : q -> qltT -> real_lt **)

let real_const_pos c _ =
  ExistT ((qdiv c { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv c { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv c { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const c) n) (projT1 real_zero n))))))))

(** val real_inv_lt_contra :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_inv_lt_contra a b ha hb hab =
  let ExistT (x, a0) = ha in
  let Pair (q0, s) = a0 in
  let ExistT (x0, q1) = s in
  let ExistT (x1, a1) = hb in
  let Pair (q2, s0) = a1 in
  let ExistT (x2, q3) = s0 in
  let ExistT (x3, a2) = hab in
  let Pair (_, s1) = a2 in
  let ExistT (x4, _) = s1 in
  let s2 = real_norm_bounded a in
  let ExistT (x5, _) = s2 in
  let s3 = real_norm_bounded b in
  let ExistT (x6, _) = s3 in
  ExistT ((qdiv x3 (qmult x5 x6)), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x3 (qmult x5 x6))), (ExistT
  ((Nat.max (Nat.max x0 x2) x4), (fun n _ ->
  qlt_to_QltT (qdiv x3 (qmult x5 x6))
    (qminus
      (projT1 (real_inv_pos a (ExistT (x, (Pair (q0, (ExistT (x0, q1))))))) n)
      (projT1 (real_inv_pos b (ExistT (x1, (Pair (q2, (ExistT (x2, q3)))))))
        n))))))))

(** val q_eps16_pos : q -> qltT -> qltT **)

let q_eps16_pos eps _ =
  qlt_to_QltT { qnum = Z0; qden = XH }
    (qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH })

(** val q_eps16_posT : q -> qltT -> qltT **)

let q_eps16_posT =
  q_eps16_pos

(** val log_testA_eps : real -> q -> q -> qltT -> q -> qltT -> bool **)

let log_testA_eps y a b _ eps heps =
  let m = qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH } in
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (exp_partial_cauchy m d4 (q_eps16_posT eps heps)) in
  let k2 = projT1 (projT2 y d4 (q_eps16_posT eps heps)) in
  qlt_bool
    (qplus (exp_partial k1 m) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (projT1 y k2)

(** val log_testB_eps : real -> q -> q -> qltT -> q -> qltT -> bool **)

let log_testB_eps y a b _ eps heps =
  let m = qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH } in
  let d4 = qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH } in
  let k1 = projT1 (exp_partial_cauchy m d4 (q_eps16_posT eps heps)) in
  let k2 = projT1 (projT2 y d4 (q_eps16_posT eps heps)) in
  qlt_bool
    (qplus (projT1 y k2) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (exp_partial k1 m)

(** val log_m_eps : q -> q -> q **)

let log_m_eps a b =
  qdiv (qplus a b) { qnum = (Zpos (XO XH)); qden = XH }

(** val log_d4_eps : q -> q **)

let log_d4_eps eps =
  qdiv eps { qnum = (Zpos (XO (XO (XO (XO XH))))); qden = XH }

(** val log_K1_eps : q -> q -> qltT -> q -> qltT -> nat **)

let log_K1_eps a b _ eps heps =
  projT1
    (exp_partial_cauchy (log_m_eps a b) (log_d4_eps eps)
      (q_eps16_posT eps heps))

(** val log_K2_eps : real -> q -> q -> qltT -> q -> qltT -> nat **)

let log_K2_eps y _ _ _ eps heps =
  projT1 (projT2 y (log_d4_eps eps) (q_eps16_posT eps heps))

(** val log_q_eps : q -> q -> qltT -> q -> qltT -> q **)

let log_q_eps a b hab eps heps =
  exp_partial (log_K1_eps a b hab eps heps) (log_m_eps a b)

(** val log_r_eps : real -> q -> q -> qltT -> q -> qltT -> q **)

let log_r_eps y a b hab eps heps =
  projT1 y (log_K2_eps y a b hab eps heps)

(** val log_testA_eps_true_lt :
    real -> q -> q -> qltT -> q -> qltT -> real_lt **)

let log_testA_eps_true_lt y a b hab eps heps =
  let d4 = log_d4_eps eps in
  let k1 = log_K1_eps a b hab eps heps in
  let k2 = log_K2_eps y a b hab eps heps in
  let q0 = log_q_eps a b hab eps heps in
  let r = log_r_eps y a b hab eps heps in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT ((Nat.max k1 k2), (fun n _ ->
  qlt_to_QltT
    (qminus (qminus r q0) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 y n)
      (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n))))))))

(** val log_testB_eps_true_gt :
    real -> q -> q -> qltT -> q -> qltT -> real_lt **)

let log_testB_eps_true_gt y a b hab eps heps =
  let d4 = log_d4_eps eps in
  let k1 = log_K1_eps a b hab eps heps in
  let k2 = log_K2_eps y a b hab eps heps in
  let q0 = log_q_eps a b hab eps heps in
  let r = log_r_eps y a b hab eps heps in
  let heps4 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
  in
  ExistT
  ((qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4)),
  (Pair (heps4, (ExistT ((Nat.max k1 k2), (fun n _ ->
  qlt_to_QltT
    (qminus (qminus q0 r) (qmult { qnum = (Zpos (XO XH)); qden = XH } d4))
    (qminus (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n)
      (projT1 y n))))))))

(** val log_test_mid_bound_eps :
    real -> q -> q -> qltT -> q -> qltT -> nat -> qleT' **)

let log_test_mid_bound_eps y a b _ eps _ n =
  qle_to_QleT'
    (qabs
      (qminus (projT1 (cauchy_real_exp (real_const (log_m_eps a b))) n)
        (projT1 y n)))
    (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))

(** val log_scan :
    real -> q -> q -> qltT -> q -> qltT -> nat -> (((q, q) prod, qltT) sigT,
    bool) prod **)

let rec log_scan y a b hab eps heps = function
| O -> Pair ((ExistT ((Pair (a, b)), hab)), True)
| S n' ->
  let m = log_m_eps a b in
  (match log_testA_eps y a b hab eps heps with
   | True -> log_scan y m b (log_mid_lt_b a b hab) eps heps n'
   | False ->
     (match log_testB_eps y a b hab eps heps with
      | True -> log_scan y a m (log_a_lt_mid a b hab) eps heps n'
      | False -> Pair ((ExistT ((Pair (a, b)), hab)), False)))

(** val log_scan_spec :
    real -> q -> q -> qltT -> q -> qltT -> nat -> real_lt -> real_lt ->
    ((bool id, (real_lt, (real_lt, qeqT) and0) and0) and0, (bool id, nat ->
    __ -> qleT') and0) or0 **)

let rec log_scan_spec y a b hab eps heps n hla hrb =
  match n with
  | O ->
    Inl (Pair (Id_refl, (Pair (hla, (Pair (hrb,
      (qeq_imp_qeqT (qminus b a)
        (qmult (qminus b a) { qnum = (Zpos XH); qden = XH }))))))))
  | S n0 ->
    let b0 = log_testA_eps y a b hab eps heps in
    (match b0 with
     | True ->
       let hmb = log_testA_eps_true_lt y a b hab eps heps in
       let hIH =
         log_scan_spec y (log_m_eps a b) b (log_mid_lt_b a b hab) eps heps n0
           hmb hrb
       in
       (match hIH with
        | Inl a0 ->
          Inl
            (let Pair (i, a1) = a0 in
             let Pair (r, a2) = a1 in
             let Pair (r0, _) = a2 in
             Pair (i, (Pair (r, (Pair (r0,
             (qeq_imp_qeqT
               (qminus
                 (snd
                   (projT1
                     (fst
                       (log_scan y (log_m_eps a b) b (log_mid_lt_b a b hab)
                         eps heps n0))))
                 (fst
                   (projT1
                     (fst
                       (log_scan y (log_m_eps a b) b (log_mid_lt_b a b hab)
                         eps heps n0)))))
               (qmult (qminus b a)
                 (q_pow
                   (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                     XH)); qden = XH })
                   (S n0))))))))))
        | Inr a0 -> Inr a0)
     | False ->
       let b1 = log_testB_eps y a b hab eps heps in
       (match b1 with
        | True ->
          let ham = log_testB_eps_true_gt y a b hab eps heps in
          let hIH =
            log_scan_spec y a (log_m_eps a b) (log_a_lt_mid a b hab) eps heps
              n0 hla ham
          in
          (match hIH with
           | Inl a0 ->
             Inl
               (let Pair (i, a1) = a0 in
                let Pair (r, a2) = a1 in
                let Pair (r0, _) = a2 in
                Pair (i, (Pair (r, (Pair (r0,
                (qeq_imp_qeqT
                  (qminus
                    (snd
                      (projT1
                        (fst
                          (log_scan y a (log_m_eps a b)
                            (log_a_lt_mid a b hab) eps heps n0))))
                    (fst
                      (projT1
                        (fst
                          (log_scan y a (log_m_eps a b)
                            (log_a_lt_mid a b hab) eps heps n0)))))
                  (qmult (qminus b a)
                    (q_pow
                      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos
                        (XO XH)); qden = XH })
                      (S n0))))))))))
           | Inr a0 -> Inr a0)
        | False ->
          Inr (Pair (Id_refl, (fun k _ ->
            log_test_mid_bound_eps y a b hab eps heps k)))))

(** val exp_lower_q : real -> real_lt -> (nat, (natLe, real_lt) and0) sigT **)

let exp_lower_q y = function
| ExistT (x, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  let h2e =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)
  in
  let hcst = real_const_pos (qdiv { qnum = (Zpos (XO XH)); qden = XH } x) h2e
  in
  let s0 =
    real_arch (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
  in
  let ExistT (x1, a0) = s0 in
  let Pair (n, r) = a0 in
  let hexpN =
    real_lt_trans (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
      (real_const { qnum = (Z.of_nat x1); qden = XH })
      (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH })) r
      (cauchy_real_exp_gt_const x1)
  in
  let hexpNpos =
    cauchy_real_exp_pos (real_const { qnum = (Z.of_nat x1); qden = XH })
  in
  ExistT (x1, (Pair (n,
  (real_eq_lt_lt
    (cauchy_real_exp (real_const (qopp { qnum = (Z.of_nat x1); qden = XH })))
    (cauchy_real_exp
      (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
    y
    (cauchy_real_exp_wd
      (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
      (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH }))
      (real_eq_of_zero_diff
        (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
        (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH }))
        (fun n0 ->
        qeq_imp_qeqT
          (qminus
            (projT1 (real_const (qopp { qnum = (Z.of_nat x1); qden = XH }))
              n0)
            (projT1
              (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })) n0))
          { qnum = Z0; qden = XH })))
    (real_lt_trans
      (cauchy_real_exp
        (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
      (real_inv_pos
        (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
      y
      (real_eq_lt_lt
        (cauchy_real_exp
          (real_opp (real_const { qnum = (Z.of_nat x1); qden = XH })))
        (real_inv_pos
          (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH }))
          hexpNpos)
        (real_inv_pos
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
        (exp_neg_recip (real_const { qnum = (Z.of_nat x1); qden = XH })
          hexpNpos)
        (real_inv_lt_contra
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
          (cauchy_real_exp (real_const { qnum = (Z.of_nat x1); qden = XH }))
          hcst hexpNpos hexpN))
      (real_eq_lt_lt
        (real_inv_pos
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
        (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) y
        (real_inv_unique
          (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
          (real_inv_pos
            (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
          (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH }))
          (real_inv_pos_correct
            (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x)) hcst)
          (real_eq_of_zero_diff
            (real_mult
              (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
              (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })))
            real_one (fun n0 ->
            qeq_imp_qeqT
              (qminus
                (projT1
                  (real_mult
                    (real_const (qdiv { qnum = (Zpos (XO XH)); qden = XH } x))
                    (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })))
                  n0)
                (projT1 real_one n0))
              { qnum = Z0; qden = XH })))
        (ExistT ((qdiv x { qnum = (Zpos (XO XH)); qden = XH }), (Pair
        ((qlt_to_QltT { qnum = Z0; qden = XH }
           (qdiv x { qnum = (Zpos (XO XH)); qden = XH })),
        (ExistT (x0, (fun n0 _ ->
        qlt_to_QltT (qdiv x { qnum = (Zpos (XO XH)); qden = XH })
          (qminus (projT1 y n0)
            (projT1
              (real_const (qdiv x { qnum = (Zpos (XO XH)); qden = XH })) n0)))))))))))))))

(** val exp_upper_q : real -> real_lt -> (nat, (natLe, real_lt) and0) sigT **)

let exp_upper_q y _ =
  let s = real_arch y in
  let ExistT (x, a) = s in
  let Pair (n, r) = a in
  ExistT (x, (Pair (n,
  (real_lt_trans y (real_const { qnum = (Z.of_nat x); qden = XH })
    (cauchy_real_exp (real_const { qnum = (Z.of_nat x); qden = XH })) r
    (cauchy_real_exp_gt_const x)))))

(** val log_lower : real -> real_lt -> q **)

let log_lower y hy =
  qopp { qnum = (Z.of_nat (projT1 (exp_lower_q y hy))); qden = XH }

(** val log_upper : real -> real_lt -> q **)

let log_upper y hy =
  { qnum = (Z.of_nat (projT1 (exp_upper_q y hy))); qden = XH }

(** val q_neg_nat_lt_nat : nat -> nat -> qltT **)

let q_neg_nat_lt_nat na nb =
  qlt_to_QltT (qopp { qnum = (Z.of_nat na); qden = XH }) { qnum =
    (Z.of_nat nb); qden = XH }

(** val q_pow_arch : q -> q -> qleT' -> qltT -> (nat, qltT) sigT **)

let q_pow_arch d eps hD heps =
  let s = arch_decay d eps hD heps in
  let ExistT (x, q0) = s in ExistT ((S x), q0)

(** val real_const_lt : q -> q -> qltT -> real_lt **)

let real_const_lt c d _ =
  ExistT ((qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH }), (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT (qdiv (qminus d c) { qnum = (Zpos (XO XH)); qden = XH })
      (qminus (projT1 (real_const d) n) (projT1 (real_const c) n))))))))

(** val real_lt_pt_lt :
    real -> real -> real_lt -> (nat, nat -> natLe -> qltT) sigT **)

let real_lt_pt_lt x y = function
| ExistT (_, a) ->
  let Pair (_, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x0, (fun k _ -> qlt_to_QltT (projT1 x k) (projT1 y k)))

(** val log_mid_strict : q -> q -> qltT -> (qltT, qltT) and0 **)

let log_mid_strict a b _ =
  Pair ((qlt_to_QltT a (log_m_eps a b)), (qlt_to_QltT (log_m_eps a b) b))

(** val exp_const_lt : q -> q -> qltT -> real_lt **)

let exp_const_lt a b hab =
  cauchy_real_exp_mono (real_const a) (real_const b) (real_const_lt a b hab)

(** val approx_span_pt :
    real -> q -> q -> qltT -> q -> q -> real_lt -> real_lt -> qleT' -> qleT'
    -> qleT' -> (nat -> qleT') -> (nat, nat -> natLe -> qleT') sigT **)

let approx_span_pt y a b haNbN _ c hla hrb _ _ _ _ =
  let m = log_m_eps a b in
  let a0 = log_mid_strict a b haNbN in
  let Pair (q0, q1) = a0 in
  let heam = exp_const_lt a (log_m_eps a b) q0 in
  let hemb = exp_const_lt (log_m_eps a b) b q1 in
  let s = real_lt_pt_lt (cauchy_real_exp (real_const a)) y hla in
  let ExistT (x, _) = s in
  let s0 = real_lt_pt_lt y (cauchy_real_exp (real_const b)) hrb in
  let ExistT (x0, _) = s0 in
  let s1 =
    real_lt_pt_lt (cauchy_real_exp (real_const a))
      (cauchy_real_exp (real_const m)) heam
  in
  let ExistT (x1, _) = s1 in
  let s2 =
    real_lt_pt_lt (cauchy_real_exp (real_const m))
      (cauchy_real_exp (real_const b)) hemb
  in
  let ExistT (x2, _) = s2 in
  ExistT ((Nat.max (Nat.max x x0) (Nat.max x1 x2)), (fun k _ ->
  let em = projT1 (cauchy_real_exp (real_const m)) k in
  let yk = projT1 y k in
  qle_to_QleT' (qabs (qminus em yk)) (qmult (qminus b a) c)))

(** val len_mul_D : q -> q -> q -> q -> q -> nat -> qeqT -> qeqT **)

let len_mul_D bN aN b0 a0 c n _ =
  qeq_imp_qeqT (qmult (qminus bN aN) c)
    (qmult (qmult (qminus b0 a0) c)
      (q_pow
        (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
          XH })
        n))

(** val real_abs_lift :
    q -> real -> q -> q -> nat -> qltT -> (nat -> natLe -> qleT') -> real_lt **)

let real_abs_lift m y m0 _UU03b3_ n0 _ _ =
  real_abs_diff_le_lift (cauchy_real_exp (real_const m)) y m0 _UU03b3_ n0

(** val approx_const_lt :
    q -> q -> q -> q -> q -> q -> nat -> qltT -> qeqT -> qeqT -> qltT **)

let approx_const_lt bN aN _ c _UU03b3_ eps _ _ _ _ =
  qlt_to_QltT (qplus (qmult (qminus bN aN) c) _UU03b3_) eps

(** val approx_def_test :
    real -> q -> q -> qltT -> nat -> (nat -> natLe -> qleT') -> real_lt **)

let approx_def_test y mN eps _ n0 hpt =
  let hlift =
    real_abs_lift mN y
      (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
      (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }) n0
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }))
      hpt
  in
  real_lt_trans
    (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
    (real_const
      (qplus
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH })))
    (real_const eps) hlift
    (real_const_lt
      (qplus
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
        (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }))
      eps
      (qlt_to_QltT
        (qplus
          (qmult { qnum = (Zpos (XO (XO XH))); qden = XH } (log_d4_eps eps))
          (qdiv eps { qnum = (Zpos (XO (XO XH))); qden = XH }))
        eps))

(** val approx_root :
    real -> real_lt -> q -> qltT -> (q, (qltT, (qltT, real_lt) and0) and0)
    sigT **)

let approx_root y hy eps heps =
  let s = exp_lower_q y hy in
  let ExistT (x, a) = s in
  let Pair (_, r) = a in
  let s0 = exp_upper_q y hy in
  let ExistT (x0, a0) = s0 in
  let Pair (_, r0) = a0 in
  let a1 = qopp { qnum = (Z.of_nat x); qden = XH } in
  let b0 = { qnum = (Z.of_nat x0); qden = XH } in
  let ha0b0 = q_neg_nat_lt_nat x x0 in
  let b = qplus (qabs a1) (qabs b0) in
  let s1 = exp_series_arch b (qle_to_QleT' { qnum = Z0; qden = XH } b) in
  let ExistT (x1, a2) = s1 in
  let Pair (_, q0) = a2 in
  let d = qmult (qminus b0 a1) x1 in
  let s2 = q_pow_arch d eps (qle_to_QleT' { qnum = Z0; qden = XH } d) heps in
  let ExistT (x2, q1) = s2 in
  let o = log_scan_spec y a1 b0 ha0b0 eps heps x2 r r0 in
  (match o with
   | Inl a3 ->
     let Pair (_, a4) = a3 in
     let Pair (r1, a5) = a4 in
     let Pair (r2, q2) = a5 in
     let abN = projT1 (fst (log_scan y a1 b0 ha0b0 eps heps x2)) in
     let aN = fst abN in
     let bN = snd abN in
     let mN = log_m_eps aN bN in
     let s3 =
       approx_span_pt y aN bN (qlt_to_QltT aN bN) b x1 r1 r2
         (qle_to_QleT' { qnum = Z0; qden = XH } b) (qle_to_QleT' (qabs aN) b)
         (qle_to_QleT' (qabs bN) b) q0
     in
     let ExistT (x3, q3) = s3 in
     ExistT (mN, (Pair
     ((qlt_to_QltT (qopp { qnum = (Z.of_nat x); qden = XH }) mN), (Pair
     ((qlt_to_QltT mN { qnum = (Z.of_nat x0); qden = XH }),
     (let hlift =
        real_abs_lift mN y (qmult (qminus bN aN) x1)
          (qdiv
            (qminus eps
              (qmult d
                (q_pow
                  (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                    XH)); qden = XH })
                  x2)))
            { qnum = (Zpos (XO XH)); qden = XH })
          x3
          (qlt_to_QltT { qnum = Z0; qden = XH }
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH }))
          q3
      in
      real_lt_trans
        (real_abs (real_plus (cauchy_real_exp (real_const mN)) (real_opp y)))
        (real_const
          (qplus (qmult (qminus bN aN) x1)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH })))
        (real_const eps) hlift
        (real_const_lt
          (qplus (qmult (qminus bN aN) x1)
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH }))
          eps
          (approx_const_lt bN aN d x1
            (qdiv
              (qminus eps
                (qmult d
                  (q_pow
                    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO
                      XH)); qden = XH })
                    x2)))
              { qnum = (Zpos (XO XH)); qden = XH })
            eps x2 q1 (len_mul_D bN aN b0 a1 x1 x2 q2)
            (qeq_imp_qeqT
              (qdiv
                (qminus eps
                  (qmult d
                    (q_pow
                      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos
                        (XO XH)); qden = XH })
                      x2)))
                { qnum = (Zpos (XO XH)); qden = XH })
              (qdiv
                (qminus eps
                  (qmult d
                    (q_pow
                      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos
                        (XO XH)); qden = XH })
                      x2)))
                { qnum = (Zpos (XO XH)); qden = XH }))))))))))
   | Inr a3 ->
     let Pair (_, q2) = a3 in
     let abN = projT1 (fst (log_scan y a1 b0 ha0b0 eps heps x2)) in
     let mN = log_m_eps (fst abN) (snd abN) in
     let n0 =
       Nat.max
         (log_K1_eps (fst abN) (snd abN)
           (projT2 (fst (log_scan y a1 b0 ha0b0 eps heps x2))) eps heps)
         (log_K2_eps y (fst abN) (snd abN)
           (projT2 (fst (log_scan y a1 b0 ha0b0 eps heps x2))) eps heps)
     in
     ExistT (mN, (Pair
     ((qlt_to_QltT (qopp { qnum = (Z.of_nat x); qden = XH }) mN), (Pair
     ((qlt_to_QltT mN { qnum = (Z.of_nat x0); qden = XH }),
     (let hptN0 = fun k _ -> q2 k __ in approx_def_test y mN eps heps n0 hptN0)))))))

(** val log_eps : nat -> q **)

let log_eps n =
  q_pow
    (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
      XH })
    (S n)

(** val log_eps_pos : nat -> qltT **)

let log_eps_pos n =
  qlt_to_QltT { qnum = Z0; qden = XH }
    (q_pow
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (S n))

(** val log_seq : real -> real_lt -> nat -> q **)

let log_seq y hy n =
  projT1 (approx_root y hy (log_eps n) (log_eps_pos n))

(** val approx_root_pt_bound :
    real -> real_lt -> nat -> (nat, nat -> natLe -> qltT) sigT **)

let approx_root_pt_bound y hy n =
  let s = approx_root y hy (log_eps n) (log_eps_pos n) in
  let ExistT (x, a) = s in
  let Pair (q0, a0) = a in
  let Pair (q1, r) = a0 in
  let s0 =
    real_lt_pt_lt
      (real_abs (real_plus (cauchy_real_exp (real_const x)) (real_opp y)))
      (real_const (log_eps n)) r
  in
  let ExistT (x0, _) = s0 in
  ExistT (x0, (fun k _ ->
  qlt_to_QltT
    (qabs
      (qminus
        (projT1
          (cauchy_real_exp
            (real_const (projT1 (ExistT (x, (Pair (q0, (Pair (q1, r)))))))))
          k)
        (projT1 y k)))
    (log_eps n)))

(** val exp_pos_shape :
    real -> (q, (qltT, (nat, nat -> natLe -> qltT) sigT) and0) sigT **)

let exp_pos_shape =
  cauchy_real_exp_pos

(** val log_seq_cauchy : real -> real_lt -> cauchy **)

let log_seq_cauchy y hy eps _ =
  let a0 = log_lower y hy in
  let s = exp_pos_shape (real_const a0) in
  let ExistT (x, _) = s in
  let delta =
    qdiv (qmult eps x) { qnum = (Zpos (XO (XO (XO XH)))); qden = XH }
  in
  let s0 =
    q_pow_arch { qnum = (Zpos XH); qden = XH } delta
      (qle_to_QleT' { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH } delta)
  in
  let ExistT (x0, _) = s0 in
  ExistT ((S x0), (fun m n _ _ ->
  qlt_to_QltT (qabs (qminus (log_seq y hy m) (log_seq y hy n))) eps))

(** val cw_log : real -> real_lt -> real **)

let cw_log y hy =
  ExistT ((log_seq y hy), (log_seq_cauchy y hy))

(** val exp_series_arch_shape :
    q -> qleT' -> (q, (qleT', nat -> qleT') and0) sigT **)

let exp_series_arch_shape =
  exp_series_arch

(** val cw_log_exp_right : real -> real_lt -> real_eq **)

let cw_log_exp_right y hy gamma _ =
  let s =
    exp_series_arch_shape
      (qplus (qabs (log_lower y hy)) (qabs (log_upper y hy)))
      (qle_to_QleT' { qnum = Z0; qden = XH }
        (qplus (qabs (log_lower y hy)) (qabs (log_upper y hy))))
  in
  let ExistT (x, _) = s in
  let hcau =
    log_seq_cauchy y hy
      (qdiv gamma
        (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
          (qplus x { qnum = (Zpos XH); qden = XH })))
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv gamma
          (qmult { qnum = (Zpos (XO (XO XH))); qden = XH }
            (qplus x { qnum = (Zpos XH); qden = XH }))))
  in
  let ExistT (x0, _) = hcau in
  let s0 =
    q_pow_arch { qnum = (Zpos XH); qden = XH }
      (qdiv gamma { qnum = (Zpos (XO (XO XH))); qden = XH })
      (qle_to_QleT' { qnum = Z0; qden = XH } { qnum = (Zpos XH); qden = XH })
      (qlt_to_QltT { qnum = Z0; qden = XH }
        (qdiv gamma { qnum = (Zpos (XO (XO XH))); qden = XH }))
  in
  let ExistT (x1, _) = s0 in
  let n0 = Nat.max x0 (S x1) in
  let happrox = approx_root_pt_bound y hy n0 in
  let ExistT (x2, _) = happrox in
  ExistT ((Nat.max n0 x2), (fun k _ ->
  qlt_to_QltT
    (qabs (qminus (projT1 (cauchy_real_exp (cw_log y hy)) k) (projT1 y k)))
    gamma))

(** val real_lt_not_eq : real -> real -> real_lt -> real_eq not **)

let real_lt_not_eq _ _ _ _ =
  assert false (* absurd case *)

(** val real_weak_trich :
    real -> real -> real_lt not -> real_lt not -> real_eq **)

let real_weak_trich x y _ _ eps _ =
  let heps3 =
    qlt_to_QltT { qnum = Z0; qden = XH }
      (qdiv eps { qnum = (Zpos (XI XH)); qden = XH })
  in
  let s = projT2 x (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) heps3 in
  let ExistT (x0, _) = s in
  let s0 = projT2 y (qdiv eps { qnum = (Zpos (XI XH)); qden = XH }) heps3 in
  let ExistT (x1, _) = s0 in
  let n = Nat.max x0 x1 in
  let hmain = fun n0 ->
    let s1 = qlt_le_dec (qabs (qminus (projT1 x n0) (projT1 y n0))) eps in
    (match s1 with
     | Left -> qlt_to_QltT (qabs (qminus (projT1 x n0) (projT1 y n0))) eps
     | Right -> assert false (* absurd case *))
  in
  ExistT (n, (fun n0 _ -> hmain n0))

(** val log_inv_one_thm : real_lt -> real_eq **)

let log_inv_one_thm h =
  let u = cw_log real_one h in
  let hright = cw_log_exp_right real_one h in
  real_weak_trich u real_zero (fun hult ->
    real_lt_not_eq (cauchy_real_exp u) (cauchy_real_exp real_zero)
      (cauchy_real_exp_mono u real_zero hult)
      (real_eq_trans (cauchy_real_exp u) real_one (cauchy_real_exp real_zero)
        hright
        (real_eq_sym (cauchy_real_exp real_zero) real_one
          cauchy_real_exp_zero)))
    (fun h0lt ->
    real_lt_not_eq (cauchy_real_exp real_zero) (cauchy_real_exp u)
      (cauchy_real_exp_mono real_zero u h0lt)
      (real_eq_trans (cauchy_real_exp real_zero) real_one (cauchy_real_exp u)
        cauchy_real_exp_zero
        (real_eq_sym (cauchy_real_exp u) real_one hright)))

(** val log_inv_mult_thm :
    real -> real -> real_lt -> real_lt -> real_lt -> real_eq **)

let log_inv_mult_thm a b ha hb hab =
  let l = cw_log (real_mult a b) hab in
  let r = real_plus (cw_log a ha) (cw_log b hb) in
  let hL = cw_log_exp_right (real_mult a b) hab in
  let hplus = cauchy_real_exp_plus (cw_log a ha) (cw_log b hb) in
  let hRa = cw_log_exp_right a ha in
  let hRb = cw_log_exp_right b hb in
  let hR =
    real_eq_trans (cauchy_real_exp r)
      (real_mult (cauchy_real_exp (cw_log a ha))
        (cauchy_real_exp (cw_log b hb)))
      (real_mult a b) hplus
      (RealSetoid.real_eq_mult_compat (cauchy_real_exp (cw_log a ha))
        (cauchy_real_exp (cw_log b hb)) a b hRa hRb)
  in
  real_weak_trich l r (fun hLlt ->
    real_lt_not_eq (cauchy_real_exp l) (cauchy_real_exp r)
      (cauchy_real_exp_mono l r hLlt)
      (real_eq_trans (cauchy_real_exp l) (real_mult a b) (cauchy_real_exp r)
        hL (real_eq_sym (cauchy_real_exp r) (real_mult a b) hR)))
    (fun hRlt ->
    real_lt_not_eq (cauchy_real_exp r) (cauchy_real_exp l)
      (cauchy_real_exp_mono r l hRlt)
      (real_eq_trans (cauchy_real_exp r) (real_mult a b) (cauchy_real_exp l)
        hR (real_eq_sym (cauchy_real_exp l) (real_mult a b) hL)))

(** val real_mult_lt_compat :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_lt_compat a b c hab hc =
  let ExistT (x, a0) = hab in
  let Pair (_, s) = a0 in
  let ExistT (x0, _) = s in
  let ExistT (x1, a1) = hc in
  let Pair (_, s0) = a1 in
  let ExistT (x2, _) = s0 in
  ExistT ((qmult x x1), (Pair
  ((qlt_to_QltT { qnum = Z0; qden = XH } (qmult x x1)), (ExistT
  ((Nat.max x0 x2), (fun n _ ->
  qlt_to_QltT (qmult x x1)
    (qminus (projT1 (real_mult b c) n) (projT1 (real_mult a c) n))))))))

(** val real_mult_lt_compat_l :
    real -> real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_lt_compat_l a b c hab hc =
  real_eq_lt_lt (real_mult c a) (real_mult a c) (real_mult c b)
    (real_mult_comm c a)
    (real_lt_eq_lt (real_mult a c) (real_mult b c) (real_mult c b)
      (real_mult_lt_compat a b c hab hc) (real_mult_comm b c))

(** val real_inv_pos_lt_contra :
    real -> real -> real_lt -> real_lt -> real_lt -> real_lt **)

let real_inv_pos_lt_contra a b ha hb hab =
  real_eq_lt_lt (real_inv_pos b hb)
    (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
    (real_inv_pos a ha)
    (real_eq_trans (real_inv_pos b hb)
      (real_mult real_one (real_inv_pos b hb))
      (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
      (real_eq_sym (real_mult real_one (real_inv_pos b hb))
        (real_inv_pos b hb)
        (real_eq_trans (real_mult real_one (real_inv_pos b hb))
          (real_mult (real_inv_pos b hb) real_one) (real_inv_pos b hb)
          (real_mult_comm real_one (real_inv_pos b hb))
          (real_mult_one (real_inv_pos b hb))))
      (RealSetoid.real_eq_mult_compat real_one (real_inv_pos b hb)
        (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb)
        (real_eq_sym (real_mult (real_inv_pos a ha) a) real_one
          (real_eq_trans (real_mult (real_inv_pos a ha) a)
            (real_mult a (real_inv_pos a ha)) real_one
            (real_mult_comm (real_inv_pos a ha) a)
            (real_inv_pos_correct a ha)))
        (real_eq_refl (real_inv_pos b hb))))
    (real_lt_eq_lt
      (real_mult (real_mult (real_inv_pos a ha) a) (real_inv_pos b hb))
      (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
      (real_inv_pos a ha)
      (real_mult_lt_compat (real_mult (real_inv_pos a ha) a)
        (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb)
        (real_mult_lt_compat_l a b (real_inv_pos a ha) hab
          (real_inv_pos_pos a ha))
        (real_inv_pos_pos b hb))
      (real_eq_trans
        (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
        (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
        (real_inv_pos a ha)
        (real_eq_sym
          (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
          (real_mult (real_mult (real_inv_pos a ha) b) (real_inv_pos b hb))
          (real_mult_assoc (real_inv_pos a ha) b (real_inv_pos b hb)))
        (real_eq_trans
          (real_mult (real_inv_pos a ha) (real_mult b (real_inv_pos b hb)))
          (real_mult (real_inv_pos a ha) real_one) (real_inv_pos a ha)
          (RealSetoid.real_eq_mult_compat (real_inv_pos a ha)
            (real_mult b (real_inv_pos b hb)) (real_inv_pos a ha) real_one
            (real_eq_refl (real_inv_pos a ha)) (real_inv_pos_correct b hb))
          (real_mult_one (real_inv_pos a ha)))))

(** val real_lt_plus_translate :
    real -> real -> real -> real_lt -> real_lt **)

let real_lt_plus_translate b c d = function
| ExistT (x, a) ->
  let Pair (q0, s) = a in
  let ExistT (x0, _) = s in
  ExistT (x, (Pair (q0, (ExistT (x0, (fun n _ ->
  qlt_to_QltT x (qminus (projT1 (real_plus b d) n) (projT1 (real_plus b c) n))))))))

(** val real_lt_plus_compat_lt_le :
    real -> real -> real -> real -> real_lt -> real_le -> real_lt **)

let real_lt_plus_compat_lt_le a b c d hab = function
| Inl r -> real_lt_plus_compat a b c d hab r
| Inr r ->
  real_eq_lt_lt (real_plus a c) (real_plus a d) (real_plus b d)
    (RealSetoid.real_eq_plus_compat a c a d (real_eq_refl a) r)
    (real_eq_lt_lt (real_plus a d) (real_plus d a) (real_plus b d)
      (real_plus_comm a d)
      (real_lt_eq_lt (real_plus d a) (real_plus d b) (real_plus b d)
        (real_lt_plus_translate d a b hab) (real_plus_comm d b)))

(** val real_le_plus_compat :
    real -> real -> real -> real -> real_le -> real_le -> real_le **)

let real_le_plus_compat a b c d hab hcd =
  match hab with
  | Inl r ->
    (match hcd with
     | Inl r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_lt_plus_compat a b c d r r0))
     | Inr r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_lt_plus_compat_lt_le a b c d r (RealSetoid.real_eq_le c d r0))))
  | Inr r ->
    (match hcd with
     | Inl r0 ->
       RealSetoid.real_lt_le_iff_req (real_plus a c) (real_plus b d) (Inl
         (real_eq_lt_lt (real_plus a c) (real_plus b c) (real_plus b d)
           (RealSetoid.real_eq_plus_compat a c b c r (real_eq_refl c))
           (real_lt_plus_translate b c d r0)))
     | Inr r0 ->
       RealSetoid.real_eq_le (real_plus a c) (real_plus b d)
         (RealSetoid.real_eq_plus_compat a c b d r r0))

(** val real_le_mult_compat :
    real -> real -> real -> real_lt -> real_le -> real_le **)

let real_le_mult_compat a b c hc = function
| Inl r ->
  RealSetoid.real_lt_le_iff_req (real_mult a c) (real_mult b c) (Inl
    (real_mult_lt_compat a b c r hc))
| Inr r ->
  RealSetoid.real_eq_le (real_mult a c) (real_mult b c)
    (RealSetoid.real_eq_mult_compat a c b c r (real_eq_refl c))

(** val real_lt_zero_one : real_lt **)

let real_lt_zero_one =
  ExistT
    ((qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
       XH }),
    (Pair
    ((qlt_to_QltT { qnum = Z0; qden = XH }
       (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
         XH })),
    (ExistT (O, (fun n _ ->
    qlt_to_QltT
      (qdiv { qnum = (Zpos XH); qden = XH } { qnum = (Zpos (XO XH)); qden =
        XH })
      (qminus (projT1 real_one n) (projT1 real_zero n))))))))

(** val real_mult_positive : real -> real -> real_lt -> real_lt -> real_lt **)

let real_mult_positive a b ha hb =
  real_eq_lt_lt real_zero (real_mult real_zero b) (real_mult a b)
    (real_eq_sym (real_mult real_zero b) real_zero
      (real_eq_trans (real_mult real_zero b) (real_mult b real_zero)
        real_zero (real_mult_comm real_zero b) (real_mult_zero b)))
    (real_mult_lt_compat real_zero a b ha hb)

(** val real_log : real -> real_lt -> real **)

let real_log =
  cw_log

(** val real_log_mult : real -> real -> real_lt -> real_lt -> real_eq **)

let real_log_mult a b ha hb =
  log_inv_mult_thm a b ha hb (real_mult_positive a b ha hb)

(** val real_log_one : real_lt -> real_eq **)

let real_log_one =
  log_inv_one_thm

(** val real_mult_opp_l : real -> real -> real_eq **)

let real_mult_opp_l a b =
  real_eq_of_zero_diff (real_mult a (real_opp b)) (real_opp (real_mult a b))
    (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_mult a (real_opp b)) n)
        (projT1 (real_opp (real_mult a b)) n))
      { qnum = Z0; qden = XH })

(** val real_mult_div : real -> real -> real_lt -> real_eq **)

let real_mult_div p q0 hp =
  real_eq_trans (real_mult p (real_mult q0 (real_inv_pos p hp)))
    (real_mult (real_mult p q0) (real_inv_pos p hp)) q0
    (real_mult_assoc p q0 (real_inv_pos p hp))
    (real_eq_trans (real_mult (real_mult p q0) (real_inv_pos p hp))
      (real_mult (real_mult q0 p) (real_inv_pos p hp)) q0
      (RealSetoid.real_eq_mult_compat (real_mult p q0) (real_inv_pos p hp)
        (real_mult q0 p) (real_inv_pos p hp) (real_mult_comm p q0)
        (real_eq_refl (real_inv_pos p hp)))
      (real_eq_trans (real_mult (real_mult q0 p) (real_inv_pos p hp))
        (real_mult q0 (real_mult p (real_inv_pos p hp))) q0
        (real_eq_sym (real_mult q0 (real_mult p (real_inv_pos p hp)))
          (real_mult (real_mult q0 p) (real_inv_pos p hp))
          (real_mult_assoc q0 p (real_inv_pos p hp)))
        (real_eq_trans (real_mult q0 (real_mult p (real_inv_pos p hp)))
          (real_mult q0 real_one) q0
          (RealSetoid.real_eq_mult_compat q0
            (real_mult p (real_inv_pos p hp)) q0 real_one (real_eq_refl q0)
            (real_inv_pos_correct p hp))
          (real_mult_one q0))))

(** val real_opp_opp : real -> real_eq **)

let real_opp_opp x =
  real_eq_of_zero_diff (real_opp (real_opp x)) x (fun n ->
    qeq_imp_qeqT (qminus (projT1 (real_opp (real_opp x)) n) (projT1 x n))
      { qnum = Z0; qden = XH })

(** val real_inv_one_local : real_eq **)

let real_inv_one_local =
  real_inv_unique real_one (real_inv_pos real_one real_lt_zero_one) real_one
    (real_inv_pos_correct real_one real_lt_zero_one) (real_mult_one real_one)

(** val real_distrib_r_local : real -> real -> real -> real_eq **)

let real_distrib_r_local x y z0 =
  real_eq_trans (real_plus (real_mult x z0) (real_mult y z0))
    (real_plus (real_mult z0 x) (real_mult z0 y))
    (real_mult (real_plus x y) z0)
    (RealSetoid.real_eq_plus_compat (real_mult x z0) (real_mult y z0)
      (real_mult z0 x) (real_mult z0 y) (real_mult_comm x z0)
      (real_mult_comm y z0))
    (real_eq_trans (real_plus (real_mult z0 x) (real_mult z0 y))
      (real_mult z0 (real_plus x y)) (real_mult (real_plus x y) z0)
      (real_eq_sym (real_mult z0 (real_plus x y))
        (real_plus (real_mult z0 x) (real_mult z0 y)) (real_distrib z0 x y))
      (real_mult_comm z0 (real_plus x y)))

(** val b4_const_eq : q -> q -> real_eq **)

let b4_const_eq _ _ _ heps =
  ExistT (O, (fun _ _ -> heps))

(** val b4_const_plus_one : q -> real_eq **)

let b4_const_plus_one c =
  real_eq_of_zero_diff (real_plus (real_const c) real_one)
    (real_const (qplus c { qnum = (Zpos XH); qden = XH })) (fun n ->
    qeq_imp_qeqT
      (qminus (projT1 (real_plus (real_const c) real_one) n)
        (projT1 (real_const (qplus c { qnum = (Zpos XH); qden = XH })) n))
      { qnum = Z0; qden = XH })

(** val b4_lift_succ : nat -> real_eq **)

let b4_lift_succ k =
  real_eq_trans (real_const { qnum = (Z.of_nat (S k)); qden = XH })
    (real_const
      (qplus { qnum = (Z.of_nat k); qden = XH } { qnum = (Zpos XH); qden =
        XH }))
    (real_plus (real_const { qnum = (Z.of_nat k); qden = XH }) real_one)
    (b4_const_eq { qnum = (Z.of_nat (S k)); qden = XH }
      (qplus { qnum = (Z.of_nat k); qden = XH } { qnum = (Zpos XH); qden =
        XH }))
    (real_eq_sym
      (real_plus (real_const { qnum = (Z.of_nat k); qden = XH }) real_one)
      (real_const
        (qplus { qnum = (Z.of_nat k); qden = XH } { qnum = (Zpos XH); qden =
          XH }))
      (b4_const_plus_one { qnum = (Z.of_nat k); qden = XH }))

(** val sf_real_plus_zero_l : real -> real_eq **)

let sf_real_plus_zero_l x =
  real_eq_of_zero_diff (real_plus real_zero x) x (fun n ->
    qeq_imp_qeqT (qminus (projT1 (real_plus real_zero x) n) (projT1 x n))
      { qnum = Z0; qden = XH })

(** val real_lt_le_bridge : real -> real -> real_lt -> real_le **)

let real_lt_le_bridge _ _ h =
  Inl h

(** val real_eq_le_bridge : real -> real -> real_eq -> real_le **)

let real_eq_le_bridge _ _ h =
  Inr h

module BudgetReal =
 struct
  (** val real_pow : real -> nat -> real **)

  let rec real_pow x = function
  | O -> real_one
  | S m -> real_mult x (real_pow x m)

  (** val real_pow_eq_compat : real -> real -> nat -> real_eq -> real_eq **)

  let rec real_pow_eq_compat x y n hxy =
    match n with
    | O -> real_eq_refl (real_pow y O)
    | S n0 ->
      RealSetoid.real_eq_mult_compat x (real_pow x n0) y (real_pow y n0) hxy
        (real_pow_eq_compat x y n0 hxy)

  (** val cwe_real_pow_pos : real -> nat -> real_lt -> real_lt **)

  let rec cwe_real_pow_pos x n hx =
    match n with
    | O -> real_lt_zero_one
    | S n0 ->
      real_mult_pos_compat x (real_pow x n0) hx (cwe_real_pow_pos x n0 hx)

  (** val real_const_zero_thm : real_eq **)

  let real_const_zero_thm =
    real_eq_of_zero_diff (real_const { qnum = (Z.of_nat O); qden = XH })
      real_zero (fun n ->
      qeq_imp_qeqT
        (qminus (projT1 (real_const { qnum = (Z.of_nat O); qden = XH }) n)
          (projT1 real_zero n))
        { qnum = Z0; qden = XH })

  (** val real_mult_one_l : real -> real_eq **)

  let real_mult_one_l x =
    real_eq_trans (real_mult real_one x) (real_mult x real_one) x
      (real_mult_comm real_one x) (real_mult_one x)

  (** val real_mult_zero_l : real -> real_eq **)

  let real_mult_zero_l x =
    real_eq_trans (real_mult real_zero x) (real_mult x real_zero) real_zero
      (real_mult_comm real_zero x) (real_mult_zero x)

  (** val real_nat_mult_succ : nat -> real -> real_eq **)

  let real_nat_mult_succ n x =
    real_eq_trans
      (real_mult (real_const { qnum = (Z.of_nat (S n)); qden = XH }) x)
      (real_mult
        (real_plus (real_const { qnum = (Z.of_nat n); qden = XH }) real_one)
        x)
      (real_plus
        (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x) x)
      (RealSetoid.real_eq_mult_compat
        (real_const { qnum = (Z.of_nat (S n)); qden = XH }) x
        (real_plus (real_const { qnum = (Z.of_nat n); qden = XH }) real_one)
        x (b4_lift_succ n) (real_eq_refl x))
      (real_eq_trans
        (real_mult
          (real_plus (real_const { qnum = (Z.of_nat n); qden = XH }) real_one)
          x)
        (real_plus
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x)
          (real_mult real_one x))
        (real_plus
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x) x)
        (real_eq_sym
          (real_plus
            (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x)
            (real_mult real_one x))
          (real_mult
            (real_plus (real_const { qnum = (Z.of_nat n); qden = XH })
              real_one)
            x)
          (real_distrib_r_local
            (real_const { qnum = (Z.of_nat n); qden = XH }) real_one x))
        (RealSetoid.real_eq_plus_compat
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x)
          (real_mult real_one x)
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x) x
          (real_eq_refl
            (real_mult (real_const { qnum = (Z.of_nat n); qden = XH }) x))
          (real_mult_one_l x)))

  (** val real_pow_inv_pair : real -> real_lt -> nat -> real_eq **)

  let rec real_pow_inv_pair k hk = function
  | O -> real_mult_one real_one
  | S n0 ->
    real_eq_trans
      (real_mult (real_mult k (real_pow k n0))
        (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0)))
      (real_mult (real_mult (real_pow k n0) k)
        (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0)))
      real_one
      (RealSetoid.real_eq_mult_compat (real_mult k (real_pow k n0))
        (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0))
        (real_mult (real_pow k n0) k)
        (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0))
        (real_mult_comm k (real_pow k n0))
        (real_eq_refl
          (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0))))
      (real_eq_trans
        (real_mult (real_mult (real_pow k n0) k)
          (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0)))
        (real_mult (real_pow k n0)
          (real_mult k
            (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0))))
        real_one
        (real_eq_sym
          (real_mult (real_pow k n0)
            (real_mult k
              (real_mult (real_inv_pos k hk)
                (real_pow (real_inv_pos k hk) n0))))
          (real_mult (real_mult (real_pow k n0) k)
            (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0)))
          (real_mult_assoc (real_pow k n0) k
            (real_mult (real_inv_pos k hk) (real_pow (real_inv_pos k hk) n0))))
        (real_eq_trans
          (real_mult (real_pow k n0)
            (real_mult k
              (real_mult (real_inv_pos k hk)
                (real_pow (real_inv_pos k hk) n0))))
          (real_mult (real_pow k n0)
            (real_mult (real_mult k (real_inv_pos k hk))
              (real_pow (real_inv_pos k hk) n0)))
          real_one
          (RealSetoid.real_eq_mult_compat (real_pow k n0)
            (real_mult k
              (real_mult (real_inv_pos k hk)
                (real_pow (real_inv_pos k hk) n0)))
            (real_pow k n0)
            (real_mult (real_mult k (real_inv_pos k hk))
              (real_pow (real_inv_pos k hk) n0))
            (real_eq_refl (real_pow k n0))
            (real_mult_assoc k (real_inv_pos k hk)
              (real_pow (real_inv_pos k hk) n0)))
          (real_eq_trans
            (real_mult (real_pow k n0)
              (real_mult (real_mult k (real_inv_pos k hk))
                (real_pow (real_inv_pos k hk) n0)))
            (real_mult (real_pow k n0)
              (real_mult real_one (real_pow (real_inv_pos k hk) n0)))
            real_one
            (RealSetoid.real_eq_mult_compat (real_pow k n0)
              (real_mult (real_mult k (real_inv_pos k hk))
                (real_pow (real_inv_pos k hk) n0))
              (real_pow k n0)
              (real_mult real_one (real_pow (real_inv_pos k hk) n0))
              (real_eq_refl (real_pow k n0))
              (RealSetoid.real_eq_mult_compat
                (real_mult k (real_inv_pos k hk))
                (real_pow (real_inv_pos k hk) n0) real_one
                (real_pow (real_inv_pos k hk) n0) (real_inv_pos_correct k hk)
                (real_eq_refl (real_pow (real_inv_pos k hk) n0))))
            (real_eq_trans
              (real_mult (real_pow k n0)
                (real_mult real_one (real_pow (real_inv_pos k hk) n0)))
              (real_mult (real_pow k n0) (real_pow (real_inv_pos k hk) n0))
              real_one
              (RealSetoid.real_eq_mult_compat (real_pow k n0)
                (real_mult real_one (real_pow (real_inv_pos k hk) n0))
                (real_pow k n0) (real_pow (real_inv_pos k hk) n0)
                (real_eq_refl (real_pow k n0))
                (real_mult_one_l (real_pow (real_inv_pos k hk) n0)))
              (real_pow_inv_pair k hk n0)))))

  (** val cwe_real_le_one_plus : real -> real_le -> real_le **)

  let cwe_real_le_one_plus x hx =
    real_le_trans real_one (real_plus real_one real_zero)
      (real_plus real_one x)
      (real_eq_le_bridge real_one (real_plus real_one real_zero)
        (real_eq_sym (real_plus real_one real_zero) real_one
          (real_plus_zero real_one)))
      (real_le_plus_compat real_one real_one real_zero x
        (real_le_refl real_one) hx)

  (** val real_lt_plus_one : real -> real_lt **)

  let real_lt_plus_one y =
    real_eq_lt_lt y (real_plus real_zero y) (real_plus real_one y)
      (real_eq_sym (real_plus real_zero y) y (sf_real_plus_zero_l y))
      (real_lt_plus_compat_lt_le real_zero real_one y y real_lt_zero_one
        (real_le_refl y))

  (** val real_nat_mult_nonneg : nat -> real -> real_lt -> real_le **)

  let rec real_nat_mult_nonneg n x hx =
    match n with
    | O ->
      real_eq_le_bridge real_zero
        (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) x)
        (real_eq_trans real_zero (real_mult real_zero x)
          (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) x)
          (real_eq_sym (real_mult real_zero x) real_zero (real_mult_zero_l x))
          (RealSetoid.real_eq_mult_compat real_zero x
            (real_const { qnum = (Z.of_nat O); qden = XH }) x
            (real_eq_sym (real_const { qnum = (Z.of_nat O); qden = XH })
              real_zero real_const_zero_thm)
            (real_eq_refl x)))
    | S n0 ->
      real_lt_le_bridge real_zero
        (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) x)
        (real_lt_eq_lt real_zero
          (real_plus
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x) x)
          (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) x)
          (real_lt_eq_lt real_zero
            (real_plus x
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x))
            (real_plus
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x)
              x)
            (real_eq_lt_lt real_zero (real_plus real_zero real_zero)
              (real_plus x
                (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x))
              (real_eq_sym (real_plus real_zero real_zero) real_zero
                (real_plus_zero real_zero))
              (real_lt_plus_compat_lt_le real_zero x real_zero
                (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x)
                hx (real_nat_mult_nonneg n0 x hx)))
            (real_plus_comm x
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x)))
          (real_eq_sym
            (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) x)
            (real_plus
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) x)
              x)
            (real_nat_mult_succ n0 x)))

  (** val bernoulli_pow : real -> real_lt -> nat -> real_le **)

  let rec bernoulli_pow c hc = function
  | O ->
    real_le_trans
      (real_plus real_one
        (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) c))
      real_one real_one
      (real_eq_le_bridge
        (real_plus real_one
          (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) c))
        real_one
        (real_eq_trans
          (real_plus real_one
            (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) c))
          (real_plus real_one real_zero) real_one
          (RealSetoid.real_eq_plus_compat real_one
            (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) c)
            real_one real_zero (real_eq_refl real_one)
            (real_eq_trans
              (real_mult (real_const { qnum = (Z.of_nat O); qden = XH }) c)
              (real_mult real_zero c) real_zero
              (RealSetoid.real_eq_mult_compat
                (real_const { qnum = (Z.of_nat O); qden = XH }) c real_zero c
                real_const_zero_thm (real_eq_refl c))
              (real_mult_zero_l c)))
          (real_plus_zero real_one)))
      (real_le_refl real_one)
  | S n0 ->
    let iH = bernoulli_pow c hc n0 in
    real_le_trans
      (real_plus real_one
        (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) c))
      (real_plus
        (real_plus real_one
          (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c))
        c)
      (real_mult (real_plus real_one c) (real_pow (real_plus real_one c) n0))
      (real_eq_le_bridge
        (real_plus real_one
          (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) c))
        (real_plus
          (real_plus real_one
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c))
          c)
        (real_eq_trans
          (real_plus real_one
            (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) c))
          (real_plus real_one
            (real_plus
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c)
              c))
          (real_plus
            (real_plus real_one
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c))
            c)
          (RealSetoid.real_eq_plus_compat real_one
            (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH }) c)
            real_one
            (real_plus
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c)
              c)
            (real_eq_refl real_one) (real_nat_mult_succ n0 c))
          (real_plus_assoc real_one
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c) c)))
      (real_le_trans
        (real_plus
          (real_plus real_one
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c))
          c)
        (real_plus (real_pow (real_plus real_one c) n0)
          (real_mult c (real_pow (real_plus real_one c) n0)))
        (real_mult (real_plus real_one c)
          (real_pow (real_plus real_one c) n0))
        (let hx0 = real_nat_mult_nonneg n0 c hc in
         let h1P =
           real_le_trans real_one
             (real_plus real_one
               (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c))
             (real_pow (real_plus real_one c) n0)
             (cwe_real_le_one_plus
               (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c)
               hx0)
             iH
         in
         real_le_plus_compat
           (real_plus real_one
             (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH }) c))
           (real_pow (real_plus real_one c) n0) c
           (real_mult c (real_pow (real_plus real_one c) n0)) iH
           (real_le_trans c (real_mult c real_one)
             (real_mult c (real_pow (real_plus real_one c) n0))
             (real_eq_le_bridge c (real_mult c real_one)
               (real_eq_sym (real_mult c real_one) c (real_mult_one c)))
             (real_le_trans (real_mult c real_one) (real_mult real_one c)
               (real_mult c (real_pow (real_plus real_one c) n0))
               (real_eq_le_bridge (real_mult c real_one)
                 (real_mult real_one c) (real_mult_comm c real_one))
               (real_le_trans (real_mult real_one c)
                 (real_mult (real_pow (real_plus real_one c) n0) c)
                 (real_mult c (real_pow (real_plus real_one c) n0))
                 (real_le_mult_compat real_one
                   (real_pow (real_plus real_one c) n0) c hc h1P)
                 (real_eq_le_bridge
                   (real_mult (real_pow (real_plus real_one c) n0) c)
                   (real_mult c (real_pow (real_plus real_one c) n0))
                   (real_mult_comm (real_pow (real_plus real_one c) n0) c))))))
        (real_eq_le_bridge
          (real_plus (real_pow (real_plus real_one c) n0)
            (real_mult c (real_pow (real_plus real_one c) n0)))
          (real_mult (real_plus real_one c)
            (real_pow (real_plus real_one c) n0))
          (real_eq_trans
            (real_plus (real_pow (real_plus real_one c) n0)
              (real_mult c (real_pow (real_plus real_one c) n0)))
            (real_plus
              (real_mult real_one (real_pow (real_plus real_one c) n0))
              (real_mult c (real_pow (real_plus real_one c) n0)))
            (real_mult (real_plus real_one c)
              (real_pow (real_plus real_one c) n0))
            (RealSetoid.real_eq_plus_compat
              (real_pow (real_plus real_one c) n0)
              (real_mult c (real_pow (real_plus real_one c) n0))
              (real_mult real_one (real_pow (real_plus real_one c) n0))
              (real_mult c (real_pow (real_plus real_one c) n0))
              (real_eq_sym
                (real_mult real_one (real_pow (real_plus real_one c) n0))
                (real_pow (real_plus real_one c) n0)
                (real_mult_one_l (real_pow (real_plus real_one c) n0)))
              (real_eq_refl
                (real_mult c (real_pow (real_plus real_one c) n0))))
            (real_distrib_r_local real_one c
              (real_pow (real_plus real_one c) n0)))))

  (** val r_arch_pow_real :
      real -> real_lt -> real_lt -> real -> real_lt -> real -> real_lt ->
      (nat, real_lt) sigT **)

  let r_arch_pow_real kappa hk1 hk2 a ha eps heps =
    let hinvpos = real_inv_pos_pos kappa hk1 in
    let honeLtInv =
      real_eq_lt_lt real_one (real_inv_pos real_one real_lt_zero_one)
        (real_inv_pos kappa hk1)
        (real_eq_sym (real_inv_pos real_one real_lt_zero_one) real_one
          real_inv_one_local)
        (real_inv_pos_lt_contra kappa real_one hk1 real_lt_zero_one hk2)
    in
    let hc = real_lt_opp_plus real_one (real_inv_pos kappa hk1) honeLtInv in
    let hax =
      real_mult_pos_compat a (real_inv_pos eps heps) ha
        (real_inv_pos_pos eps heps)
    in
    let c = real_plus (real_inv_pos kappa hk1) (real_opp real_one) in
    let x = real_mult a (real_inv_pos eps heps) in
    let s = real_arch (real_mult x (real_inv_pos c hc)) in
    let ExistT (x0, a0) = s in
    let Pair (_, r) = a0 in
    let hxc_lt =
      real_eq_lt_lt x (real_mult (real_mult x (real_inv_pos c hc)) c)
        (real_mult (real_const { qnum = (Z.of_nat x0); qden = XH }) c)
        (real_eq_trans x (real_mult c (real_mult x (real_inv_pos c hc)))
          (real_mult (real_mult x (real_inv_pos c hc)) c)
          (real_eq_sym (real_mult c (real_mult x (real_inv_pos c hc))) x
            (real_mult_div c x hc))
          (real_mult_comm c (real_mult x (real_inv_pos c hc))))
        (real_mult_lt_compat (real_mult x (real_inv_pos c hc))
          (real_const { qnum = (Z.of_nat x0); qden = XH }) c r hc)
    in
    let honec =
      real_eq_trans
        (real_plus real_one
          (real_plus (real_inv_pos kappa hk1) (real_opp real_one)))
        (real_plus (real_plus real_one (real_inv_pos kappa hk1))
          (real_opp real_one))
        (real_inv_pos kappa hk1)
        (real_plus_assoc real_one (real_inv_pos kappa hk1)
          (real_opp real_one))
        (real_eq_trans
          (real_plus (real_plus real_one (real_inv_pos kappa hk1))
            (real_opp real_one))
          (real_plus (real_plus (real_inv_pos kappa hk1) real_one)
            (real_opp real_one))
          (real_inv_pos kappa hk1)
          (RealSetoid.real_eq_plus_compat
            (real_plus real_one (real_inv_pos kappa hk1)) (real_opp real_one)
            (real_plus (real_inv_pos kappa hk1) real_one) (real_opp real_one)
            (real_plus_comm real_one (real_inv_pos kappa hk1))
            (real_eq_refl (real_opp real_one)))
          (real_eq_trans
            (real_plus (real_plus (real_inv_pos kappa hk1) real_one)
              (real_opp real_one))
            (real_plus (real_inv_pos kappa hk1)
              (real_plus real_one (real_opp real_one)))
            (real_inv_pos kappa hk1)
            (real_eq_sym
              (real_plus (real_inv_pos kappa hk1)
                (real_plus real_one (real_opp real_one)))
              (real_plus (real_plus (real_inv_pos kappa hk1) real_one)
                (real_opp real_one))
              (real_plus_assoc (real_inv_pos kappa hk1) real_one
                (real_opp real_one)))
            (real_eq_trans
              (real_plus (real_inv_pos kappa hk1)
                (real_plus real_one (real_opp real_one)))
              (real_plus (real_inv_pos kappa hk1) real_zero)
              (real_inv_pos kappa hk1)
              (RealSetoid.real_eq_plus_compat (real_inv_pos kappa hk1)
                (real_plus real_one (real_opp real_one))
                (real_inv_pos kappa hk1) real_zero
                (real_eq_refl (real_inv_pos kappa hk1))
                (real_plus_opp real_one))
              (real_plus_zero (real_inv_pos kappa hk1)))))
    in
    let hkey =
      real_lt_eq_lt x (real_pow (real_plus real_one c) x0)
        (real_pow (real_inv_pos kappa hk1) x0)
        (real_lt_le_trans x
          (real_plus real_one
            (real_mult (real_const { qnum = (Z.of_nat x0); qden = XH }) c))
          (real_pow (real_plus real_one c) x0)
          (real_lt_trans x
            (real_mult (real_const { qnum = (Z.of_nat x0); qden = XH }) c)
            (real_plus real_one
              (real_mult (real_const { qnum = (Z.of_nat x0); qden = XH }) c))
            hxc_lt
            (real_lt_plus_one
              (real_mult (real_const { qnum = (Z.of_nat x0); qden = XH }) c)))
          (bernoulli_pow c hc x0))
        (real_pow_eq_compat (real_plus real_one c) (real_inv_pos kappa hk1)
          x0 honec)
    in
    let hposN = cwe_real_pow_pos (real_inv_pos kappa hk1) x0 hinvpos in
    let hpowinv =
      real_inv_unique (real_pow (real_inv_pos kappa hk1) x0)
        (real_pow kappa x0)
        (real_inv_pos (real_pow (real_inv_pos kappa hk1) x0) hposN)
        (real_eq_trans
          (real_mult (real_pow (real_inv_pos kappa hk1) x0)
            (real_pow kappa x0))
          (real_mult (real_pow kappa x0)
            (real_pow (real_inv_pos kappa hk1) x0))
          real_one
          (real_mult_comm (real_pow (real_inv_pos kappa hk1) x0)
            (real_pow kappa x0))
          (real_pow_inv_pair kappa hk1 x0))
        (real_inv_pos_correct (real_pow (real_inv_pos kappa hk1) x0) hposN)
    in
    let hinva =
      real_inv_unique x (real_inv_pos x hax)
        (real_mult eps (real_inv_pos a ha)) (real_inv_pos_correct x hax)
        (real_eq_trans (real_mult x (real_mult eps (real_inv_pos a ha)))
          (real_mult a
            (real_mult (real_inv_pos eps heps)
              (real_mult eps (real_inv_pos a ha))))
          real_one
          (real_eq_sym
            (real_mult a
              (real_mult (real_inv_pos eps heps)
                (real_mult eps (real_inv_pos a ha))))
            (real_mult (real_mult a (real_inv_pos eps heps))
              (real_mult eps (real_inv_pos a ha)))
            (real_mult_assoc a (real_inv_pos eps heps)
              (real_mult eps (real_inv_pos a ha))))
          (real_eq_trans
            (real_mult a
              (real_mult (real_inv_pos eps heps)
                (real_mult eps (real_inv_pos a ha))))
            (real_mult a
              (real_mult (real_mult (real_inv_pos eps heps) eps)
                (real_inv_pos a ha)))
            real_one
            (RealSetoid.real_eq_mult_compat a
              (real_mult (real_inv_pos eps heps)
                (real_mult eps (real_inv_pos a ha)))
              a
              (real_mult (real_mult (real_inv_pos eps heps) eps)
                (real_inv_pos a ha))
              (real_eq_refl a)
              (real_mult_assoc (real_inv_pos eps heps) eps
                (real_inv_pos a ha)))
            (real_eq_trans
              (real_mult a
                (real_mult (real_mult (real_inv_pos eps heps) eps)
                  (real_inv_pos a ha)))
              (real_mult a (real_mult real_one (real_inv_pos a ha))) real_one
              (RealSetoid.real_eq_mult_compat a
                (real_mult (real_mult (real_inv_pos eps heps) eps)
                  (real_inv_pos a ha))
                a (real_mult real_one (real_inv_pos a ha)) (real_eq_refl a)
                (RealSetoid.real_eq_mult_compat
                  (real_mult (real_inv_pos eps heps) eps) (real_inv_pos a ha)
                  real_one (real_inv_pos a ha)
                  (real_eq_trans (real_mult (real_inv_pos eps heps) eps)
                    (real_mult eps (real_inv_pos eps heps)) real_one
                    (real_mult_comm (real_inv_pos eps heps) eps)
                    (real_inv_pos_correct eps heps))
                  (real_eq_refl (real_inv_pos a ha))))
              (real_eq_trans
                (real_mult a (real_mult real_one (real_inv_pos a ha)))
                (real_mult a (real_inv_pos a ha)) real_one
                (RealSetoid.real_eq_mult_compat a
                  (real_mult real_one (real_inv_pos a ha)) a
                  (real_inv_pos a ha) (real_eq_refl a)
                  (real_mult_one_l (real_inv_pos a ha)))
                (real_inv_pos_correct a ha)))))
    in
    let hinvlt =
      real_inv_pos_lt_contra x (real_pow (real_inv_pos kappa hk1) x0) hax
        hposN hkey
    in
    let hklt =
      real_eq_lt_lt (real_pow kappa x0)
        (real_inv_pos (real_pow (real_inv_pos kappa hk1) x0) hposN)
        (real_mult eps (real_inv_pos a ha)) hpowinv
        (real_lt_eq_lt
          (real_inv_pos (real_pow (real_inv_pos kappa hk1) x0) hposN)
          (real_inv_pos x hax) (real_mult eps (real_inv_pos a ha)) hinvlt
          hinva)
    in
    ExistT (x0,
    (real_lt_eq_lt (real_mult a (real_pow kappa x0))
      (real_mult a (real_mult eps (real_inv_pos a ha))) eps
      (real_mult_lt_compat_l (real_pow kappa x0)
        (real_mult eps (real_inv_pos a ha)) a hklt ha)
      (real_mult_div a eps ha)))

  (** val real_pow_log_form : real -> real_lt -> nat -> real_eq **)

  let rec real_pow_log_form k hk = function
  | O ->
    real_eq_trans (real_log (real_pow k O) (cwe_real_pow_pos k O hk))
      real_zero
      (real_mult (real_const { qnum = (Z.of_nat O); qden = XH })
        (real_log k hk))
      (real_log_one (cwe_real_pow_pos k O hk))
      (real_eq_sym
        (real_mult (real_const { qnum = (Z.of_nat O); qden = XH })
          (real_log k hk))
        real_zero
        (real_eq_trans
          (real_mult (real_const { qnum = (Z.of_nat O); qden = XH })
            (real_log k hk))
          (real_mult real_zero (real_log k hk)) real_zero
          (RealSetoid.real_eq_mult_compat
            (real_const { qnum = (Z.of_nat O); qden = XH }) (real_log k hk)
            real_zero (real_log k hk) real_const_zero_thm
            (real_eq_refl (real_log k hk)))
          (real_mult_zero_l (real_log k hk))))
  | S n0 ->
    real_eq_trans
      (real_log (real_mult k (real_pow k n0)) (cwe_real_pow_pos k (S n0) hk))
      (real_plus (real_log k hk)
        (real_log (real_pow k n0) (cwe_real_pow_pos k n0 hk)))
      (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH })
        (real_log k hk))
      (log_inv_mult_thm k (real_pow k n0) hk (cwe_real_pow_pos k n0 hk)
        (cwe_real_pow_pos k (S n0) hk))
      (real_eq_trans
        (real_plus (real_log k hk)
          (real_log (real_pow k n0) (cwe_real_pow_pos k n0 hk)))
        (real_plus (real_log k hk)
          (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
            (real_log k hk)))
        (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH })
          (real_log k hk))
        (RealSetoid.real_eq_plus_compat (real_log k hk)
          (real_log (real_pow k n0) (cwe_real_pow_pos k n0 hk))
          (real_log k hk)
          (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
            (real_log k hk))
          (real_eq_refl (real_log k hk)) (real_pow_log_form k hk n0))
        (real_eq_trans
          (real_plus (real_log k hk)
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
              (real_log k hk)))
          (real_plus
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
              (real_log k hk))
            (real_log k hk))
          (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH })
            (real_log k hk))
          (real_plus_comm (real_log k hk)
            (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
              (real_log k hk)))
          (real_eq_trans
            (real_plus
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
                (real_log k hk))
              (real_log k hk))
            (real_plus
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
                (real_log k hk))
              (real_log k hk))
            (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH })
              (real_log k hk))
            (RealSetoid.real_eq_plus_compat
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
                (real_log k hk))
              (real_log k hk)
              (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
                (real_log k hk))
              (real_log k hk)
              (real_eq_refl
                (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
                  (real_log k hk)))
              (real_eq_refl (real_log k hk)))
            (real_eq_sym
              (real_mult (real_const { qnum = (Z.of_nat (S n0)); qden = XH })
                (real_log k hk))
              (real_plus
                (real_mult (real_const { qnum = (Z.of_nat n0); qden = XH })
                  (real_log k hk))
                (real_log k hk))
              (real_nat_mult_succ n0 (real_log k hk))))))

  (** val budget_cond_sufficient :
      real -> real -> real -> real_lt -> real_lt -> real_lt -> real_lt -> nat
      -> real_lt -> real_lt **)

  let budget_cond_sufficient kappa a eps hk1 _ ha heps n hcond =
    let hlogpow =
      real_eq_trans
        (real_log (real_mult a (real_pow kappa n))
          (real_mult_positive a (real_pow kappa n) ha
            (cwe_real_pow_pos kappa n hk1)))
        (real_plus (real_log a ha)
          (real_log (real_pow kappa n) (cwe_real_pow_pos kappa n hk1)))
        (real_plus (real_log a ha)
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
            (real_log kappa hk1)))
        (real_log_mult a (real_pow kappa n) ha (cwe_real_pow_pos kappa n hk1))
        (RealSetoid.real_eq_plus_compat (real_log a ha)
          (real_log (real_pow kappa n) (cwe_real_pow_pos kappa n hk1))
          (real_log a ha)
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
            (real_log kappa hk1))
          (real_eq_refl (real_log a ha)) (real_pow_log_form kappa hk1 n))
    in
    let hnegm =
      real_eq_trans
        (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
          (real_log kappa hk1))
        (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
          (real_opp (real_opp (real_log kappa hk1))))
        (real_opp
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
            (real_opp (real_log kappa hk1))))
        (RealSetoid.real_eq_mult_compat
          (real_const { qnum = (Z.of_nat n); qden = XH })
          (real_log kappa hk1)
          (real_const { qnum = (Z.of_nat n); qden = XH })
          (real_opp (real_opp (real_log kappa hk1)))
          (real_eq_refl (real_const { qnum = (Z.of_nat n); qden = XH }))
          (real_eq_sym (real_opp (real_opp (real_log kappa hk1)))
            (real_log kappa hk1) (real_opp_opp (real_log kappa hk1))))
        (real_mult_opp_l (real_const { qnum = (Z.of_nat n); qden = XH })
          (real_opp (real_log kappa hk1)))
    in
    let hmid =
      real_eq_lt_lt (real_log a ha)
        (real_plus (real_plus (real_log a ha) (real_opp (real_log eps heps)))
          (real_log eps heps))
        (real_plus
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
            (real_opp (real_log kappa hk1)))
          (real_log eps heps))
        (real_eq_trans (real_log a ha)
          (real_plus (real_log a ha)
            (real_plus (real_opp (real_log eps heps)) (real_log eps heps)))
          (real_plus
            (real_plus (real_log a ha) (real_opp (real_log eps heps)))
            (real_log eps heps))
          (real_eq_sym
            (real_plus (real_log a ha)
              (real_plus (real_opp (real_log eps heps)) (real_log eps heps)))
            (real_log a ha)
            (real_eq_trans
              (real_plus (real_log a ha)
                (real_plus (real_opp (real_log eps heps)) (real_log eps heps)))
              (real_plus (real_log a ha) real_zero) (real_log a ha)
              (RealSetoid.real_eq_plus_compat (real_log a ha)
                (real_plus (real_opp (real_log eps heps)) (real_log eps heps))
                (real_log a ha) real_zero (real_eq_refl (real_log a ha))
                (real_eq_trans
                  (real_plus (real_opp (real_log eps heps))
                    (real_log eps heps))
                  (real_plus (real_log eps heps)
                    (real_opp (real_log eps heps)))
                  real_zero
                  (real_plus_comm (real_opp (real_log eps heps))
                    (real_log eps heps))
                  (real_plus_opp (real_log eps heps))))
              (real_plus_zero (real_log a ha))))
          (real_plus_assoc (real_log a ha) (real_opp (real_log eps heps))
            (real_log eps heps)))
        (real_lt_plus_compat_lt_le
          (real_plus (real_log a ha) (real_opp (real_log eps heps)))
          (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
            (real_opp (real_log kappa hk1)))
          (real_log eps heps) (real_log eps heps) hcond
          (real_le_refl (real_log eps heps)))
    in
    let hshift = fun x0 la0 le0 w0 h1 h2 ->
      real_eq_lt_lt x0 (real_plus la0 (real_opp w0)) le0 h1
        (real_lt_eq_lt (real_plus la0 (real_opp w0))
          (real_plus (real_plus w0 le0) (real_opp w0)) le0
          (real_lt_plus_compat_lt_le la0 (real_plus w0 le0) (real_opp w0)
            (real_opp w0) h2 (real_le_refl (real_opp w0)))
          (real_eq_trans (real_plus (real_plus w0 le0) (real_opp w0))
            (real_plus w0 (real_plus le0 (real_opp w0))) le0
            (real_eq_sym (real_plus w0 (real_plus le0 (real_opp w0)))
              (real_plus (real_plus w0 le0) (real_opp w0))
              (real_plus_assoc w0 le0 (real_opp w0)))
            (real_eq_trans (real_plus w0 (real_plus le0 (real_opp w0)))
              (real_plus (real_plus w0 (real_opp w0)) le0) le0
              (real_eq_trans (real_plus w0 (real_plus le0 (real_opp w0)))
                (real_plus w0 (real_plus (real_opp w0) le0))
                (real_plus (real_plus w0 (real_opp w0)) le0)
                (RealSetoid.real_eq_plus_compat w0
                  (real_plus le0 (real_opp w0)) w0
                  (real_plus (real_opp w0) le0) (real_eq_refl w0)
                  (real_plus_comm le0 (real_opp w0)))
                (real_plus_assoc w0 (real_opp w0) le0))
              (real_eq_trans (real_plus (real_plus w0 (real_opp w0)) le0)
                (real_plus real_zero le0) le0
                (RealSetoid.real_eq_plus_compat (real_plus w0 (real_opp w0))
                  le0 real_zero le0 (real_plus_opp w0) (real_eq_refl le0))
                (sf_real_plus_zero_l le0)))))
    in
    let hlt =
      hshift
        (real_log (real_mult a (real_pow kappa n))
          (real_mult_positive a (real_pow kappa n) ha
            (cwe_real_pow_pos kappa n hk1)))
        (real_log a ha) (real_log eps heps)
        (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
          (real_opp (real_log kappa hk1)))
        (real_eq_trans
          (real_log (real_mult a (real_pow kappa n))
            (real_mult_positive a (real_pow kappa n) ha
              (cwe_real_pow_pos kappa n hk1)))
          (real_plus (real_log a ha)
            (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
              (real_log kappa hk1)))
          (real_plus (real_log a ha)
            (real_opp
              (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
                (real_opp (real_log kappa hk1)))))
          hlogpow
          (RealSetoid.real_eq_plus_compat (real_log a ha)
            (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
              (real_log kappa hk1))
            (real_log a ha)
            (real_opp
              (real_mult (real_const { qnum = (Z.of_nat n); qden = XH })
                (real_opp (real_log kappa hk1))))
            (real_eq_refl (real_log a ha)) hnegm))
        hmid
    in
    real_eq_lt_lt (real_mult a (real_pow kappa n))
      (cauchy_real_exp
        (real_log (real_mult a (real_pow kappa n))
          (real_mult_positive a (real_pow kappa n) ha
            (cwe_real_pow_pos kappa n hk1))))
      eps
      (real_eq_sym
        (cauchy_real_exp
          (cw_log (real_mult a (real_pow kappa n))
            (real_mult_positive a (real_pow kappa n) ha
              (cwe_real_pow_pos kappa n hk1))))
        (real_mult a (real_pow kappa n))
        (cw_log_exp_right (real_mult a (real_pow kappa n))
          (real_mult_positive a (real_pow kappa n) ha
            (cwe_real_pow_pos kappa n hk1))))
      (real_lt_eq_lt
        (cauchy_real_exp
          (real_log (real_mult a (real_pow kappa n))
            (real_mult_positive a (real_pow kappa n) ha
              (cwe_real_pow_pos kappa n hk1))))
        (cauchy_real_exp (real_log eps heps)) eps
        (cauchy_real_exp_mono
          (real_log (real_mult a (real_pow kappa n))
            (real_mult_positive a (real_pow kappa n) ha
              (cwe_real_pow_pos kappa n hk1)))
          (real_log eps heps) hlt)
        (cw_log_exp_right eps heps))

  (** val real_pow_add_thm : real -> nat -> nat -> real_eq **)

  let rec real_pow_add_thm k p j =
    match p with
    | O ->
      real_eq_sym (real_mult real_one (real_pow k j)) (real_pow k j)
        (real_mult_one_l (real_pow k j))
    | S n ->
      real_eq_trans (real_mult k (real_pow k (add n j)))
        (real_mult k (real_mult (real_pow k n) (real_pow k j)))
        (real_mult (real_pow k (S n)) (real_pow k j))
        (RealSetoid.real_eq_mult_compat k (real_pow k (add n j)) k
          (real_mult (real_pow k n) (real_pow k j)) (real_eq_refl k)
          (real_pow_add_thm k n j))
        (real_eq_trans
          (real_mult k (real_mult (real_pow k n) (real_pow k j)))
          (real_mult (real_mult k (real_pow k n)) (real_pow k j))
          (real_mult (real_pow k (S n)) (real_pow k j))
          (real_mult_assoc k (real_pow k n) (real_pow k j))
          (real_eq_refl (real_mult (real_pow k (S n)) (real_pow k j))))

  (** val real_pow_le_one : real -> real_lt -> real_le -> nat -> real_le **)

  let rec real_pow_le_one k hk1 hk2 = function
  | O -> real_le_refl real_one
  | S n ->
    real_le_trans (real_mult k (real_pow k n)) (real_mult k real_one)
      real_one
      (real_le_trans (real_mult k (real_pow k n))
        (real_mult (real_pow k n) k) (real_mult k real_one)
        (real_eq_le_bridge (real_mult k (real_pow k n))
          (real_mult (real_pow k n) k) (real_mult_comm k (real_pow k n)))
        (real_le_trans (real_mult (real_pow k n) k) (real_mult real_one k)
          (real_mult k real_one)
          (real_le_mult_compat (real_pow k n) real_one k hk1
            (real_pow_le_one k hk1 hk2 n))
          (real_eq_le_bridge (real_mult real_one k) (real_mult k real_one)
            (real_eq_trans (real_mult real_one k) k (real_mult k real_one)
              (real_mult_one_l k)
              (real_eq_sym (real_mult k real_one) k (real_mult_one k))))))
      (real_le_trans (real_mult k real_one) k real_one
        (real_eq_le_bridge (real_mult k real_one) k (real_mult_one k)) hk2)

  (** val real_pow_anti_mono :
      real -> real_lt -> real_le -> nat -> nat -> real_le **)

  let real_pow_anti_mono k hk1 hk2 p q0 =
    let j = sub q0 p in
    let heq = real_pow_add_thm k p j in
    real_le_trans (real_pow k (add p j))
      (real_mult (real_pow k p) (real_pow k j)) (real_pow k p)
      (real_eq_le_bridge (real_pow k (add p j))
        (real_mult (real_pow k p) (real_pow k j)) heq)
      (real_le_trans (real_mult (real_pow k p) (real_pow k j))
        (real_mult (real_pow k j) (real_pow k p)) (real_pow k p)
        (real_eq_le_bridge (real_mult (real_pow k p) (real_pow k j))
          (real_mult (real_pow k j) (real_pow k p))
          (real_mult_comm (real_pow k p) (real_pow k j)))
        (real_le_trans (real_mult (real_pow k j) (real_pow k p))
          (real_mult real_one (real_pow k p)) (real_pow k p)
          (real_le_mult_compat (real_pow k j) real_one (real_pow k p)
            (cwe_real_pow_pos k p hk1) (real_pow_le_one k hk1 hk2 j))
          (real_eq_le_bridge (real_mult real_one (real_pow k p))
            (real_pow k p) (real_mult_one_l (real_pow k p)))))

  (** val geo_tail_budget :
      real -> real -> real -> real_lt -> real_lt -> real_lt -> real_lt -> nat
      -> nat -> nat -> real_lt -> real_lt **)

  let geo_tail_budget kappa a eps hk1 hk2 ha _ m n n0 hbudget =
    let hk2le = real_lt_le_bridge kappa real_one hk2 in
    real_le_lt_trans (real_mult a (real_pow kappa (min m n)))
      (real_mult a (real_pow kappa n0)) eps
      (real_le_trans (real_mult a (real_pow kappa (min m n)))
        (real_mult (real_pow kappa (min m n)) a)
        (real_mult a (real_pow kappa n0))
        (real_eq_le_bridge (real_mult a (real_pow kappa (min m n)))
          (real_mult (real_pow kappa (min m n)) a)
          (real_mult_comm a (real_pow kappa (min m n))))
        (real_le_trans (real_mult (real_pow kappa (min m n)) a)
          (real_mult (real_pow kappa n0) a) (real_mult a (real_pow kappa n0))
          (real_le_mult_compat (real_pow kappa (min m n)) (real_pow kappa n0)
            a ha (real_pow_anti_mono kappa hk1 hk2le n0 (min m n)))
          (real_eq_le_bridge (real_mult (real_pow kappa n0) a)
            (real_mult a (real_pow kappa n0))
            (real_mult_comm (real_pow kappa n0) a))))
      hbudget

  (** val budget_min_tail :
      real -> real -> real -> real_lt -> real_lt -> real_lt -> real_lt ->
      (nat, nat -> nat -> __ -> real_lt) sigT **)

  let budget_min_tail kappa a eps hk1 hk2 ha heps =
    let s = r_arch_pow_real kappa hk1 hk2 a ha eps heps in
    let ExistT (x, r) = s in
    ExistT (x, (fun p q0 _ ->
    geo_tail_budget kappa a eps hk1 hk2 ha heps p q0 x r))
 end
