typed;

type Stream[A] = /\X (/\S (S -> (S -> S) -> (S -> A) -> X) -> X);

type Sum[A,B] = /\X ((A -> X) -> (B -> X) -> X);

let ileft = /\A/\B \a.(\f g. f a) : Sum[A,B];
let iright = /\A/\B \b.(\f g. g b) : Sum[A,B];
let case = /\A/\B \s : Sum[A,B] f g.s f g;

let pack = /\A \s f a.(\g.g s f a) : Stream[A];

let head = /\A \s:Stream[A].s \s1 f a.a s1;

let tail = /\A \s:Stream[A].s \s1 f a.pack (f s1) f a ;

let map = \s f.pack s tail \s.f (head s);

let cons =/\A \a s.pack (ileft a):Sum[A,Stream[A]]
              (\x.case x (\a.iright s) (\s.iright (tail s))) 
              (\x.case x (\a.a)       (\s.head s));

include "nat.typ";

let all_int = pack 0 (\x.add x 1) \x.x; 


(*
this is not typable !

let get_state = /\A \s:Stream[A]. s \s f a.s;
*)