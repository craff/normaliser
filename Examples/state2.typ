typed;

#include "list.typ";
#include "nat.typ";
#include "triple.typ";

type V[W,T] = List[T];
type Var[W] = Nat;
type State[W,T,X] = Var[W] -> V[W,T] -> Triple[Var[W],V[W,T],X];
type Unit = /\X (X -> X);

let unit : /\X/\W/\T(X -> State[W,T,X]) x = fun n v => triple n v x;

let bind : /\X/\Y/\W/\T (State[W,T,X] -> (X -> State[W,T,Y]) -> State[W,T,Y]);
  \t f n l. t n l (\n' l' x. f x n' l'); 

let read : /\X/\W/\T 
  (Var[W] -> (T -> State[W,T,X]) -> State[W,T,X]) =
  \v f n l -> triple n l (f (nth (sub n v) l) n l)
;

let write : /\X/\W/\T 
  (Var[W] -> T -> State[W,T,Unit]) =
  \v t n l. triple (S n) (cons t l) (f (nth (sub n v) l) n l)
;

let write : /\V (V -> State[V,Unit]) =
  \x v. pair x (\x.x);
let run : /\V/\X (State[V,X] -> V  -> X) = \n v. pi2 (n v);

