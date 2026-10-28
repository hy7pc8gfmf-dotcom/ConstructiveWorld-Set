
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

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

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

type natLe = bool id

(** val natLe_lift : nat -> nat -> natLe **)

let natLe_lift n m =
  let b = Nat.leb n m in
  (match b with
   | True -> Id_refl
   | False -> assert false (* absurd case *))

type qseq = nat -> q

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

(** val qltT_0_2 : qltT **)

let qltT_0_2 =
  Id_refl

(** val qleT'_trans : q -> q -> q -> qleT' -> qleT' -> qleT' **)

let qleT'_trans x _ z0 _ _ =
  qle_to_QleT' x z0

(** val qleT'_ltT_ltT : q -> q -> q -> qleT' -> qltT -> qltT **)

let qleT'_ltT_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_leT'_ltT : q -> q -> q -> qltT -> qleT' -> qltT **)

let qltT_leT'_ltT x _ z0 _ _ =
  qlt_to_QltT x z0

(** val qltT_plus_ltT : q -> q -> q -> q -> qltT -> qltT -> qltT **)

let qltT_plus_ltT a b c d _ _ =
  qlt_to_QltT (qplus a c) (qplus b d)

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

(** val qltT_div_pos : q -> q -> qltT -> qltT -> qltT **)

let qltT_div_pos x y _ _ =
  qlt_to_QltT { qnum = Z0; qden = XH } (qdiv x y)

(** val qltT_eq_compat_l : q -> q -> q -> qeqT -> qltT -> qltT **)

let qltT_eq_compat_l _ a' b _ _ =
  qlt_to_QltT a' b

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

(** val real_lt_zero_minus : real -> real -> real_lt -> real_lt **)

let real_lt_zero_minus x y = function
| ExistT (x0, a) ->
  let Pair (q0, s) = a in
  let ExistT (x1, _) = s in
  ExistT (x0, (Pair (q0, (ExistT (x1, (fun n _ ->
  qlt_to_QltT x0 (qminus (projT1 y n) (projT1 x n))))))))

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
 end

(** val one_minus_delta_pos_real : real -> real_lt -> real_lt **)

let one_minus_delta_pos_real delta hd =
  real_lt_opp_plus delta real_one hd

(** val one_minus_delta_lt_one_real : real -> real_lt -> real_lt **)

let one_minus_delta_lt_one_real delta hd =
  real_lt_zero_minus (real_plus real_one (real_opp delta)) real_one
    (real_lt_eq_lt real_zero delta
      (real_plus real_one (real_opp (real_plus real_one (real_opp delta))))
      hd
      (real_eq_sym
        (real_plus real_one (real_opp (real_plus real_one (real_opp delta))))
        delta
        (real_eq_of_zero_diff
          (real_plus real_one
            (real_opp (real_plus real_one (real_opp delta))))
          delta (fun n ->
          qeq_imp_qeqT
            (qminus
              (projT1
                (real_plus real_one
                  (real_opp (real_plus real_one (real_opp delta))))
                n)
              (projT1 delta n))
            { qnum = Z0; qden = XH }))))

(** val r_arch_pow_attn_real :
    real -> real_lt -> real_lt -> real -> real_lt -> real -> real_lt -> (nat,
    real_lt) sigT **)

let r_arch_pow_attn_real delta hd1 hd2 a ha eps heps =
  BudgetReal.r_arch_pow_real (real_plus real_one (real_opp delta))
    (one_minus_delta_pos_real delta hd2)
    (one_minus_delta_lt_one_real delta hd1) a ha eps heps

(** val tv_iter_decay_real :
    real -> real_lt -> real_lt -> (nat -> real) -> (nat -> real_le) -> nat ->
    real_le **)

let tv_iter_decay_real delta _ hd2 tv_seq hstep n =
  let hk1 = one_minus_delta_pos_real delta hd2 in
  let kappa = real_plus real_one (real_opp delta) in
  let rec f = function
  | O ->
    real_eq_le_bridge (tv_seq O)
      (real_mult (BudgetReal.real_pow kappa O) (tv_seq O))
      (real_eq_sym (real_mult (BudgetReal.real_pow kappa O) (tv_seq O))
        (tv_seq O) (BudgetReal.real_mult_one_l (tv_seq O)))
  | S n1 ->
    real_le_trans (tv_seq (S n1)) (real_mult kappa (tv_seq n1))
      (real_mult (BudgetReal.real_pow kappa (S n1)) (tv_seq O)) (hstep n1)
      (real_le_trans (real_mult kappa (tv_seq n1))
        (real_mult (tv_seq n1) kappa)
        (real_mult (BudgetReal.real_pow kappa (S n1)) (tv_seq O))
        (real_eq_le_bridge (real_mult kappa (tv_seq n1))
          (real_mult (tv_seq n1) kappa) (real_mult_comm kappa (tv_seq n1)))
        (real_le_trans (real_mult (tv_seq n1) kappa)
          (real_mult (real_mult (BudgetReal.real_pow kappa n1) (tv_seq O))
            kappa)
          (real_mult (BudgetReal.real_pow kappa (S n1)) (tv_seq O))
          (real_le_mult_compat (tv_seq n1)
            (real_mult (BudgetReal.real_pow kappa n1) (tv_seq O)) kappa hk1
            (f n1))
          (real_eq_le_bridge
            (real_mult (real_mult (BudgetReal.real_pow kappa n1) (tv_seq O))
              kappa)
            (real_mult (BudgetReal.real_pow kappa (S n1)) (tv_seq O))
            (real_eq_trans
              (real_mult
                (real_mult (BudgetReal.real_pow kappa n1) (tv_seq O)) kappa)
              (real_mult kappa
                (real_mult (BudgetReal.real_pow kappa n1) (tv_seq O)))
              (real_mult (real_mult kappa (BudgetReal.real_pow kappa n1))
                (tv_seq O))
              (real_mult_comm
                (real_mult (BudgetReal.real_pow kappa n1) (tv_seq O)) kappa)
              (real_mult_assoc kappa (BudgetReal.real_pow kappa n1)
                (tv_seq O))))))
  in f n

(** val attention_iterate_converges_real :
    real -> real_lt -> real_lt -> (nat -> real) -> (nat -> real_le) -> real
    -> real_lt -> real_lt -> (nat, nat -> __ -> real_lt) sigT **)

let attention_iterate_converges_real delta hd1 hd2 tv_seq hstep eps heps htv0 =
  let s = r_arch_pow_attn_real delta hd1 hd2 (tv_seq O) htv0 eps heps in
  let ExistT (x, r) = s in
  ExistT (x, (fun n _ ->
  let kappa = real_plus real_one (real_opp delta) in
  real_le_lt_trans (tv_seq n)
    (real_mult (BudgetReal.real_pow kappa n) (tv_seq O)) eps
    (tv_iter_decay_real delta hd1 hd2 tv_seq hstep n)
    (real_le_lt_trans (real_mult (BudgetReal.real_pow kappa n) (tv_seq O))
      (real_mult (BudgetReal.real_pow kappa x) (tv_seq O)) eps
      (let hk1 = one_minus_delta_pos_real delta hd2 in
       let hk2le =
         real_lt_le_bridge kappa real_one
           (one_minus_delta_lt_one_real delta hd1)
       in
       let hanti = BudgetReal.real_pow_anti_mono kappa hk1 hk2le x n in
       real_le_mult_compat (BudgetReal.real_pow kappa n)
         (BudgetReal.real_pow kappa x) (tv_seq O) htv0 hanti)
      (real_eq_lt_lt (real_mult (BudgetReal.real_pow kappa x) (tv_seq O))
        (real_mult (tv_seq O) (BudgetReal.real_pow kappa x)) eps
        (real_mult_comm (BudgetReal.real_pow kappa x) (tv_seq O)) r))))
