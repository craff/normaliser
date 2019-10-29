typed;

fun x:/\X X => x:\/X X;

untyped fun x:\/X X => x:/\X X;

type I = /\X (X -> X);
type I' = \/X (X -> X);

fun x:/\X ((X -> X) -> (X -> X)) => x:(I -> I);
untyped fun x:/\X ((X -> X) -> (X -> X)) => x:(I' -> I);

fun x:(I' -> I) => x:/\X ((X -> X) -> I) ;
fun x:/\X ((X -> X) -> I) => x:(I' -> I) ;
fun x:\/X ((X -> X) -> I) => x:(I -> I) ;
untyped fun x:(I -> I) => x:\/X ((X -> X) -> I) ;

fun x:(I -> I) => x:/\X (I -> (X -> X)) ;
fun x:/\X (I -> (X -> X)) => x:(I -> I) ;
fun x:\/X (I -> (X -> X)) => x:(I -> I') ;
untyped fun x:(I -> I') => x:\/X (I -> (X -> X)) ;

fun x:I => x:/\X\/Y (X -> Y);
fun x:I => x:/\X\/Y (Y -> X);
untyped fun x:I => x:\/Y/\X (X -> Y);
untyped fun x:I => x:\/Y/\X (Y -> X);

inductive;

type F[K] = /\X (X -> (K -> X) -> X);
type G[X,K] = (X -> (K -> X) -> X);
type S = !K F[K];
type G = ?K F[K];

fun x:S => x:G;
(* loop untyped fun x:G => x:S; *)

fun x:S => x:F[S];
fun x:S => x:F[F[S]];
fun x:F[S] => x:S;
fun x:F[F[S]] => x:S;

fun x:G => x:F[G];
fun x:G => x:F[F[G]];
fun x:F[G] => x:G;
fun x:F[F[G]] => x:G;

type F2[K,L] = /\X (X -> (K -> X) -> (L -> X) -> X);
type P1 = !K F2[K,K];
type P2 = !K1!K2 F2[K1,K2];
type P3 = !K1?K2 F2[K1,K2]; (* if K1 is for zeros : only a finite number of 0 *)
type P4 = ?K2!K1 F2[K1,K2]; (* only finitely many consecutive zeros *)
type P5 = ?K2?K1 F2[K1,K2];
type P6 = ?K F2[K,K];

fun x:P2 => x:P1;
fun x:P1 => x:F2[P2,P2]:P2; (* needs help ! *)
type FS[K1] = !K2 F2[K1,K2]; 
fun x:P2 => x:!K1 F2[K1,FS[K1]]:P3; (* needs help ! *)
(* loop untyped fun x:P3 => x:P2; *)
(* loop untyped fun x:P4 => x:P3; *)
type FG[K2] = ?K1 F2[K1,K2]; 
fun x:P4 => x:?K2 F2[FG[K2],K2]:P5;
(* loop untyped fun x:P5 => x:P4; *)
fun x:P5 => x:F2[P5,P5]:P6;
fun x:P6 => x:P5;
(*
verbose;
fun x:P3 => x:?K2 F2[P3,K2]:!K1 F2[K1,P4]:P4;
*)
