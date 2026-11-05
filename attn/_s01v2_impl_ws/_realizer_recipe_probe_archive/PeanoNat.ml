open Datatypes

module Nat =
 struct
  (** val pred : nat -> nat **)

  let pred n = match n with
  | O -> n
  | S u -> u

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> Coq_true
    | S n' -> (match m with
               | O -> Coq_false
               | S m' -> leb n' m')
 end
