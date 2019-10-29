typed; inductive;
include "nat.typ";
include "bool.typ";
include "prod.typ";
include "error.typ";

type List[A] = /\X ((A -> X -> X) -> X -> X);

let nil = (\cs nl.nl) : /\A List[A];
let cons : /\A (A -> List[A] -> List[A]) a l = \cs nl. cs a (l cs nl);

let car : /\A (List[A] -> Err[A]) = /\A \l:List[A].l (\x y.unit x) Error;

let cdr = /\A \l:List[A].l
	     (\a p x y.p (cons a x) x)
             (\x y.y) nil nil;


let sum = \l.l:List[Nat] add 0; 

let assoc = /\X/\Y \eq : (X -> X -> Bool) x l:List[Prod[X,Y]]. l 
  (\y ys. if (eq x (pi1 y)) (unit (pi2 y)) ys) Error;

(* 
let l = cons (pair 3 4) (cons (pair 5 6) nil);
assoc eqN 3 l;
assoc eqN 5 l;
assoc eqN 4 l;
*)

