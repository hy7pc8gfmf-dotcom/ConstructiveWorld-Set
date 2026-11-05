
type bool =
| Coq_true
| Coq_false

type nat =
| O
| S of nat

type ('a, 'b) prod =
| Coq_pair of 'a * 'b

type 'a list =
| Coq_nil
| Coq_cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Coq_nil -> O
| Coq_cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Coq_nil -> m
  | Coq_cons (a, l1) -> Coq_cons (a, (app l1 m))
