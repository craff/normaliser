# church numeral, very classical but very bad representation ! 

typed;

type Nat = /\X ((X -> X) -> X -> X);

let 0 = (\f x.x) : Nat;
let S = \n:Nat.(\f x.f (n f x)):Nat;
let 1 = S 0; let 2 = S 1; let 3 = S 2; let 4 = S 3;
let 5 = S 4; let 6 = S 5; let 7 = S 6; let 8 = S 7;
let 9 = S 8; let 10 = S 9;
let add = \n:Nat m:Nat.(\f x.n f (m f x)) : Nat;
let mul = \n:Nat m:Nat.(\f.n (m f)):Nat;
let 20 = add 10 10; let 30 = add 20 10;
let 40 = add 30 10; let 100 = mul 10 10;

let pred = \n:Nat.(n 
        (\p x y.p (S x) x)
        (\x y.y) 0 0);

include "prod.typ";

let pred = \n:Nat.pi2 (n 
        (\p. pair (S (pi1 p)) (pi1 p))
        (pair 0 0));

let pred = \n:Nat.(n 
        (\p.p \x y p.p ((\n:Nat.(\f x.f (n f x))) x) x)
        (\p.p 0 0)):Prod[Nat,Nat] (\x y.y);

include "bool.typ";

inductive; (* this term require inductive types *)

let leq = \n:Nat m:Nat. n (\f g.g f) (\i.True)
                        (m (\f g.g f) (\i.False));
