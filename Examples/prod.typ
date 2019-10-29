typed;

type Prod[A,B] = /\X ((A -> B -> X) -> X);

let pair = (\x y f. f x y) : /\A /\B (A -> B -> Prod[A,B]);
let pi1 = /\A/\B \x : Prod[A,B]. (x (\x:A y:B.x));
let pi2 = /\A/\B \x : Prod[A,B]. (x (\x:A y:B.y));

type Prod3[A,B,C] = /\X ((A -> B -> C -> X) -> X);

let pair3 = (\x y z f. f x y z) : /\A /\B /\C (A -> B -> C -> Prod3[A,B,C]);
let pi1_3 = /\A/\B/\C \x : Prod[A,B,C]. (x (\x y z.x));
let pi2_3 = /\A/\B/\C \x : Prod[A,B,C]. (x (\x y z.y));
let pi3_3 = /\A/\B/\C \x : Prod[A,B,C]. (x (\x y z.z));


type Sum[A,B] = /\X ((A -> X) -> (B -> X) -> X);
let inl = (\x f g. f x) : /\A /\B (A -> Sum[A,B]);
let inr = (\x f g. g x) : /\A /\B (B -> Sum[A,B]);
let case = \x. x;