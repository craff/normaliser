Bool = /\X (X -> X -> X);
Nat = /\X ((X -> X) -> X -> X);
List[A] = /\X ((A -> X -> X) -> X -> X);
Nat_Star[O] = /\X (((X -> O) -> (X -> O)) -> (X -> O) -> (X -> O));
Bool_Star[O] = /\X ((X -> O) -> (X -> O) -> (X -> O));
List_Star[A,O] = /\X ((A -> (X -> O) -> (X -> O)) -> (X -> O) -> (X -> O));

s = \n.\f.\x. (f (n f x)) : Nat -> Nat;

zero =\f.\x. x : Nat;

false = \x.\y. y : Bool;

true= \x.\y. x : Bool;    

nil= \f.\x. x : /\X List[X];

cons =\b.\l.\f.\x. (f b (l f x)) : /\X (X -> List[X] -> List[X]);

d1= \f. (f zero);

h1= \x.\y. (x \z. (y (s z)));

nstore = \n. (n h1 d1) : /\O (Nat_Star[O] -> (Nat -> O) -> O) ;

bstore =\b. (b (\f. f true) (\f. f false)) : /\O (Bool_Star[O] -> (Bool -> O) -> O);

d2 = \f. (f nil);

h2= \a. (bstore a \b.\r.\f. (r \z. (f (cons b z))));

lstore  =\l. (l h2 d2) : /\O (List_Star[Bool,O] -> (List[Bool] -> O) -> O) ;

bB=\b.\r. (b false r);

test_list =\l.\n.\m. (l bB true n m) : List[Bool] -> Nat -> Nat -> Nat;

cons_0 = \l.\f.\x. (f false (l f x));

list =\k. (k cons_0 (cons true nil)) : Nat -> List[Bool];

not = \a.\x.\y. (a y x) : Bool -> Bool;

gG = \a.\y.\b. (b (cons a (y true)) (cons (not a) (y a)));

dD = \b. nil  ;

pred= \l. (l gG dD false) : List[Bool] -> List[Bool];

next =\g.\l. (test_list l (s (g l)) (lstore (pred l) g)) :
(List[Bool] -> Nat) -> List[Bool] -> Nat;

dif =\n.\k. (n next (\x. zero) (list k)) : Nat -> Nat -> Nat;

test=\n.\k.\a.\b. (dif n k (\x. a) b) : Nat -> Nat -> Bool -> Bool -> Bool;

init =\n.\m.\p.\q. true : Nat -> Nat -> Nat -> Nat -> Bool;

iteration =\g.\n.\m.\k.\p. 
	(m (\x. 
	n (\x. test n k (test m k (g n m (s k) k) false)
(test m k true ((nstore (dif m p) (nstore (dif n p) g)) zero zero))) true)
false) : (Nat -> Nat -> Nat -> Nat -> Bool) -> (Nat -> Nat -> Nat -> Nat -> Bool);

inf =\n.\m. (s (s (s ( s (s (s ( s (s n))))))) iteration init n m zero zero) : Nat -> Nat -> Bool;

good_inf =\n.\m. (inf n m n m);







