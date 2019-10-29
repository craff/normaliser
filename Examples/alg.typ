typed; inductive;

type Zero = [ ];

let impossible : Zero -> /\X X = fun z => case z of [ ];

type Unit = { };

let unit : Unit = { };

type Pair[A,B] = { 1 : A; 2 : B; };

type Bool = [ True; False; ];

let pair : /\A/\B (A -> B -> Pair[A,B])
  = fun a b => { 1 = a; 2 = b; };

let neg : Bool -> Bool = fun b => case b of [ True[x] -> False[];  False[] -> True[]; ] ;

type Nat = !K [ S : K; Z; ] ;

let 0 : Nat = Z[] ;

let succ : Nat -> Nat = fun n => S[n] ;

type Rel = !K [ Z; S : K; P : K; ] ;

let natrel : Nat -> Rel = fun n => n ;

let case_nat : Nat -> !K /\P ({ Z : (Unit -> P); S : (K -> P); } -> P) = fun n => n;

type T[P] = /\Y (( { Z : Unit -> Y -> P; S : Y; } -> Y -> P) -> Y -> P);

let iter_nat : /\P (Nat -> P -> (P -> P) -> P) =
  /\P fun n a f =>
    n:/\P ({S : T[P]; Z : Unit -> T[P] -> P; } -> T[P] -> P)
      { Z = (fun u x => a):(Unit -> T[P] -> P) ;
        S = (fun p x => f (p { Z = (fun u x => a); S = x; } x)):T[P] ; }
            (fun p x => f (p { Z = (fun u x => a); S = x; } x)):T[P];

let add : Nat -> Nat -> Nat = fun n m => iter_nat n m succ;
let mul : Nat -> Nat -> Nat = fun n m => iter_nat n 0 (add m);

let pred : Nat -> Nat = fun n => case n of [Z[] -> Z[] ; S[n] -> n; ];

let sub : Nat -> Nat -> Nat = fun n m => iter_nat m n pred;

type T[P] = /\Y (( { Z : Unit -> Y -> Nat -> P; S : Y; } -> Y -> Nat -> P) -> Y -> Nat -> P);

let rec_nat : /\P (Nat -> P -> (Nat -> P -> P) -> P) =
  /\P fun n a f => n:/\P ({S : T[P]; Z : Unit -> T[P] -> P; } -> T[P] -> P)
      { Z = (fun u x q => a):(Unit -> T[P] -> Nat -> P);
        S = (fun p x q => f q (p { Z = (fun u x p => a); S = x; } x (pred q))):T[P] ; }
            (fun p x q => f q (p { Z = (fun u x p => a); S = x; } x (pred q))):T[P]
	    (pred n);

let 1 = succ 0;

let 2 = add 1 1;

let 4 = add 2 2;

let 8 = add 4 4;

let 64 = mul 8 8;

let bcp = mul 64 64;

pair 64 bcp;

type List[A] = !K [ Nil; Cons : { car : A; cdr : K; }; ];

let nil = Nil[];

let cons : /\A/\B (A -> List[A] -> List[A]) = fun a l => Cons[{car = a; cdr = l;}];

type T[A,P] = /\Y ({car : A; cdr : { Nil : Unit -> Y -> P; Cons : Y; } -> Y -> P; } -> Y -> P);

let iter_list : /\A/\P (List[A] -> P -> (A -> P -> P) -> P) =
  /\A/\P fun n a f =>
    n:/\P ({Cons : T[A,P] ; Nil : Unit -> T[A,P] -> P; } -> T[A,P] -> P)
      { Nil  = (fun u x => a):(Unit -> T[A,P] -> P);
        Cons = (fun p x => f p.car (p.cdr { Nil = (fun u x => a); Cons = x; } x)):T[A,P]; }
               (fun p x => f p.car (p.cdr { Nil = (fun u x => a); Cons = x; } x)):T[A,P];

let map : /\A/\B ((A -> B) -> (List[A] -> List[B])) =
  /\A/\B fun f l => iter_list l nil:List[B] (fun a l => cons (f a) l);

(pair 2 4).1;

map succ (cons 2 (cons 4 nil));
