module Fstar

type list 'a =
  | Nil : list 'a
  | Cons : 'a -> list 'a -> list 'a
  
type rtree =
  | Node : list rtree -> rtree
  
val t : list int -> Tot int
let t x = 5

val t2: rtree -> Tot unit
let rec t2 x = 
    match x with
    | Node xs -> 
      match xs with
      | Nil -> ()
      | Cons a ys -> t2 a

// let _ = FStar.IO.print_any t2

val t3: rtree -> Tot unit
let rec t3 x = t3 x

val t4: nat -> Tot unit
let rec t4 x = if x = 0 then () else t4 (x/2)


val ackermann: m:nat -> n:nat -> Tot nat
let rec ackermann m n =
  if m=0 then n + 1
  else if n = 0 then ackermann (m - 1) 1
  else ackermann (m - 1) (ackermann m (n - 1))


  (* well founded subterm ordering with fuel *)