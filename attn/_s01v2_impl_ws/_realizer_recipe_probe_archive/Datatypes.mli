
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

val length : 'a1 list -> nat

val app : 'a1 list -> 'a1 list -> 'a1 list
