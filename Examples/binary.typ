# Binary coding of natural numbers

# boolean are needed
include "bool.typ";
include "prod.typ";
include "error.typ";

# recursive definition are used and this a typed file
recursive; typed; inductive;

type FBin[K] = /\X((K -> X) -> (K -> X) -> X -> X);
type Bin = !K FBin[K];

# Binary representation with lower bits first
let End : Bin = \z o e.e;        # end of the representation
let Sz  : Bin -> Bin = \n z o e.z n; # adds a zero
let nSz  : Bin -> Bin = \n.n (\np z o e.z n) (\np z o e.z n) End; 
   # adds a zero and keep a normal representation
let So  : Bin -> Bin = \n z o e.(o n);   # adds a one

# We will only use "normal" represention. This means we will assume
# that there is never some useless zeros at the end of a number.  To
# do this we need two functions which add a zero or a one in front of
# a normal representation, keeping it normal and caring about errors.

let eSz : Err[Bin] -> Err[Bin] 
  = \z. bind z \x. unit (Sz x);
let enSz : Err[Bin] -> Err[Bin] 
  = \z. bind z \x. unit (nSz x);
let eSo : Err[Bin] -> Err[Bin] 
  = \z. bind z \x. unit (So x);

# Test for zero (works on non normal representation)
let rec Is_zero : Bin -> Bool = \n.n
  (\np.Is_zero np)
  (\np.False)
  True
;

# Successor and zero
let Zero = End;
let rec S : Bin -> Bin = \n.n (\np.So np) (\np.Sz (S np)) (So End);

# Predecessor
let rec Pred : Bin -> Err[Bin] = \n.n 
  (\np.eSo (Pred np)) (\np.unit (nSz np)) Error;

# Addition
let rec Add_aux : Bin -> Bin -> Bool -> Bin
  = \n m r. n
  (\np.m 
    (\mp.r (So (Add_aux np mp False)) (Sz (Add_aux np mp False)))
    (\mp.r (Sz (Add_aux np mp True)) (So (Add_aux np mp False)))
    (r (So np) (Sz np)))
  (\np.m 
    (\mp.r (Sz (Add_aux np mp True)) (So (Add_aux np mp False)))
    (\mp.r (So (Add_aux np mp True)) (Sz (Add_aux np mp True)))
    (r (Sz (S np)) (So np)))
  (r (S m) m);
let Add = \n m.Add_aux n m False;

# Multiplication
let rec Mul : Bin -> Bin -> Bin = \n m.(n
  (\np.Sz (Mul np m))
  (\np.Add m (Sz (Mul np m)))
  End);

# Subtraction
let rec Sub_aux : Bin -> Bin -> Bool -> Err[Bin] = \n m r. n
  (\np.m 
    (\mp.r (eSo (Sub_aux np mp True)) (enSz (Sub_aux np mp False)))
    (\mp.r (enSz (Sub_aux np mp True)) (eSo (Sub_aux np mp True)))
    (r (eSo (Pred np)) (unit (nSz np))))
  (\np.m 
    (\mp.r (enSz (Sub_aux np mp False)) (eSo (Sub_aux np mp False)))
    (\mp.r (eSo (Sub_aux np mp True)) (enSz (Sub_aux np mp False)))
    (r (unit (nSz np)) (unit (So np))))
  (r Error (Is_zero m (unit End) Error));
let Sub = \n m.Sub_aux n m False;


# Bad Division and modulo
let rec Euclide : Bin -> Bin -> Prod[Bin,Bin] = \n m. n
  (\np. (Euclide np m \q r.
      catch (Sub (nSz r) m)
        (\nr. pair (So q) nr)
        (pair (nSz q) (nSz r))))
  (\np. (Euclide np m \q r.
      catch (Sub (So r) m)
        (\nr. pair (So q) nr)
        (pair (nSz q) (So r))))
  (pair End End)
;

let Div : Bin -> Bin -> Bin n m = pi1 (Euclide n m);
let Mod : Bin -> Bin -> Bin n m = pi2 (Euclide n m);


# Another Division and modulo
let rec Reverse' : Bin -> Bin -> Bin = fun n a =>
  n (\np.Reverse' np (Sz a)) (\np.Reverse' np (So a)) a;
let Reverse n = Reverse' n End;

let Euclide n m =
  let rec Euclide' : Bin -> Bin -> Bin -> Prod[Bin,Bin] n r q =
    catch (Sub n m)
      (\nn. r (\nr.Euclide' (nSz nn) nr (So q))
              (\nr.Euclide' (So nn) nr (So q))
              (pair (So q) nn))
      (r (\nr.Euclide' (nSz n) nr (nSz q))
         (\nr.Euclide' (So n) nr (nSz q))
         (pair (nSz q) n))
  in Euclide' End (Reverse n) End
; 

let Div : Bin -> Bin -> Bin n m = pi1 (Euclide n m);
let Mod : Bin -> Bin -> Bin n m = pi2 (Euclide n m);

# Printing in binary (High bit first)
type Unit = /\X (X -> X);

let rec Printb : Bin -> Unit n = 
  n (\np. Printb np "0") (\np. Printb np "1") "";

# Printing in decimal (quite slow)
let Print_dec : Bin -> Unit n = n
  (\np.np (\npp.npp (\x."8") (\x."4") "?") 
          (\npp.npp (\x."?") (\x."6") "2") "?")
  (\np.np (\npp.npp (\x."9") (\x."5") "?") 
          (\npp.npp (\x."?") (\x."7") "3") "1")
  "0"
;
let dix : Bin = \z o e.z (\z o e.o (\z o e.z (\z o e.o (\z o e.e))));
let rec Print : Bin -> Unit = \n. (Euclide n dix)
  (\q r. Is_zero q "" (Print q) (Print_dec r));


# Some numbers
let 0 = End;
let 1 = S 0;
let 2 = S 1;
let 3 = S 2;
let 4 = S 3;
let 5 = S 4;
let 6 = S 5;
let 7 = S 6;
let 8 = S 7;
let 9 = S 8;
let 10 = S 9;
let 20 = Add 10 10;
let 30 = Add 20 10;
let 40 = Add 30 10;
let 100 = Mul 10 10;

# A classical example:
let rec Fact = \n.Is_zero n 1 (Mul n (catch (Pred n) Fact 0));

(*
include "binary.typ";   
*)

