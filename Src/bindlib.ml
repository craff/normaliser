(* We need set of integers : *)
module Int_ord = struct 
  type t = int
  let compare = compare
end
module Set = Set.Make(Int_ord)

(* merge l l' merge two sorted list in one sorted list without repetition *)
let rec merge l l' = 
  match l, l' with
    [], l -> l
  | l, [] -> l
  | (x::ls as l),(x'::ls' as l') ->
    if x = x' then merge ls l'
    else if x <= x' then x::(merge ls l')
    else x'::(merge l ls')

(* diffs l computes the set of all (y - x) for x and y distinct in l *) 
let rec diffs = function
  [] -> Set.empty
| x::l ->
    let rec gn s = function
      [] -> s
    | y::l -> gn (Set.add (y - x) s) l
    in gn (diffs l) l

(* ppcnd l computes the smallest number n such that for any x and y distinct*)
(* in l, x mod n <> y mod n *) 
let ppcnd l =
  let n = ref (List.length l) in
  if !n < 2 then !n else
  let s = diffs l in
  try while true do
    try
      Set.iter (fun p -> if p mod !n = 0 then raise Not_found) s;
      raise Exit
    with Not_found -> incr n 
  done; 0 with Exit -> !n

(* search n l, remove the first occurrence of n in the sorted list l *)
let rec search n = function
    [] -> raise Not_found
  | n'::ls ->
      if n < n' then 
	raise Not_found
      else if n > n' then
	n'::(search n ls)
      else
      	ls

(* no comment *)
let get_next = function
  [] -> 0
| x::_ -> x


(* the exception raised when start_term is called on a non-closed term *)
exception Bindlib_error

(* the type of binder: ('a,'b) binder is an expression of type 'b with a bound*)
(* variable of type 'a *)
(*  exported abstract *)
type ('a,'b) binder = 'a -> 'b
    
(* the substitution, it is just an application ! *)
external subst : 'a -> 'a = "%identity"

(* the environment type: it is used to store the value of all bound*)
(* variables. We need the "Obj" module because all the bound variable may have*)
(* diffrent types and we want to store them in an array *)
type environment = Obj.t array

(* the type of expression of type 'a using binder and under construction *)
type 'a pre_term = 

    (* the term as no free variable *)
    Closed of 'a 

    (* the general case : *)
    (* Open(vt,bt,t): 
         what "t" means :
           if v is an array olding the value of all the free variable of the
           constructed term, the (t v) will be the this term where the free
           variable have been subsituted with their value 
         vt is the list of all free variable in the term
         bt is a list of bound variable of the term that have a place reserved
           for their value in the Aenvironment "v" you may give to "t". This is
           provided To avoid building a new array (or closure) each time you
           descend under a binder 
    *) 
  | Open of int list * int list * (environment -> 'a)

(* Construct a 'a pre_term to represent the variable numbered var 
   You can notice that we use the environment to store values as a hashtable 
   with no failure (we always find the value the first time we look for it)
   The last case in the environment is used to store the position of the next
   variable we can assign in the environment.
*)
let mk_var var = 
    Open([var], [], fun v -> Obj.magic v.(var mod (Array.length v - 1)))

(* take a ter of type 'a and turn it into a 'a pre_term taht can be used to*)
(* construct a larger term with binder *)
let unit t = Closed t

(* take a function t and an environment v and create an environment nv with*)
(* places for future values of bound variable that t needs. table is an array*)
(* containing the free variable, nsize if the required size of the new array*)
(* and next is the first bound variable that may be assigned is the new array *)
let mk_select next nsize table t v =
  let nb_global = Array.length table in
  let osize = (Array.length v) - 1 in
  let nv = Array.create (nsize + 1) (Obj.repr next) in
  for i = 0 to nb_global - 1 do
    nv.(table.(i) mod nsize) <- v.(table.(i) mod osize)
  done;
  t nv

(* select, takes a term t waiting for an environment with the value of the*)
(* free variable listed in "frees" and the value and the bound variable that*)
(* have a reserved place listed in bounds and transform it into a a term that*)
(* wait for an environment with no reserved place for bound variable *)
let select frees bounds t = 
  match bounds with
    [] -> () ,t
  | next::_ -> 
    let table = Array.of_list frees in
    let nsize = ppcnd (bounds @ frees) in
    (), (mk_select next nsize table t)

let mk_apply f a v = f v (a v)
let mk_lapply f a v = f (a v)
let mk_rapply f a v = f v a

(* the "bind" function of the monad: take an object of type ('a -> 'b)*)
(* pre_term, that is a function with some free variables, an argument of type*)
(* 'a  pre_term, and build the application, of type 'b pre_term which is a*)
(* term that may also have free variables *)
(* The function select is used here to build the "minimal" closure when both*)
(* the function and the argument have free variables *)
let apply tf ta =
  match tf, ta with
    Closed f, Closed a -> Closed (f a)
  | Closed f, Open(va,ba,a) -> 
      Open(va,ba,mk_lapply f a)
  | Open(vf,bf,f), Closed(a) -> 
      Open(vf, bf, mk_rapply f a)
  | Open(vf,bf,f), Open(va,ba,a) ->
      let vars = merge vf va in
      Open(vars, [], mk_apply (snd (select vf bf f)) (snd (select va ba a)))

(* used for a binder when you bind a variable in closed term (therefore that*)
(* variable does not occur in the term ! *)
let mk_closed_bind pt _ =
  pt

(* used for binder which binds a variable with no occurrence (but the term has*)
(* other free variables *)
let mk_mute_bind pt v _ =
  pt v

(* used for the first binder in a closed term (the binder that binds the last*)
(* free variable in a term and make it a close term *)
let mk_first_bind var_mod_size next sizep pt arg =
  let v = Array.create sizep (Obj.repr next) in
  v.(var_mod_size) <- Obj.repr arg;
  pt v

(* used for the general case of a binder *)
let mk_bind var next pt v arg =
  let size = Array.length v - 1 in
  if (Obj.magic v.(size) : int) = var then begin
    v.(size) <- Obj.repr next;
    v.(var mod size) <- Obj.repr arg;
    pt v
  end else begin
    let nv = Array.copy v in 
    nv.(size) <- Obj.repr next;
    nv.(var mod size) <- Obj.repr arg;
    pt nv
  end

(* the function taht creates the number of a new variable *)
let new_var =
  let count = ref 0 in
  fun () -> incr count; !count

(* take a function of type ('a -> 'b) pre_term and transform it into a binder*) 
(* of type ('a -> 'b) binder pre_term *)
let bind fpt =
  let v = new_var () in
  match fpt (mk_var v) with
    Closed t ->
      Closed (mk_closed_bind t)
  | Open(vt,bt,t) -> 
      try 
        match vt with
          [var] -> 
            if v <> var then raise Not_found;
            let next = get_next bt in
            let size = ppcnd (var::bt) in
            Closed (mk_first_bind (var mod size) next (size+1) t)
        |  og ->
            let ng = search v og in
            let lg = v::bt in
            let next = get_next bt in
            Open(ng, lg, mk_bind v next t) 
      with Not_found ->
	Open(vt, bt, mk_mute_bind t)

(* When a term has no free variable, you can get it ! *)
let start_term = function
    Closed t -> t
  | Open(_) -> raise Bindlib_error

(* Here are some usefull function *)
(* Some of them are optimised (the comment is the simple definition) *)

(*
let unit_apply f ta = apply (unit f) ta
*)
let unit_apply f ta =
  match ta with
    Closed a -> Closed (f a)
  | Open(va,ba,a) -> 
      Open(va, ba, mk_lapply f a)

(*
let unit_apply2 f t t' = apply (unit_apply f t) t' 
*)

let mk_apply2 f a b v = f (a v) (b v)
let mk_lapply2 f a b v = f a (b v)
let mk_rapply2 f a b v = f (a v) b

let unit_apply2 f ta tb =
  match ta, tb with
    Closed a, Closed b -> Closed (f a b)
  | Closed a, Open(vb,bb,b) -> 
      Open(vb, bb, mk_lapply2 f a b)
  | Open(va,ba,a), Closed(b) -> 
      Open(va, ba, mk_rapply2 f a b)
  | Open(va,ba,a), Open(vb,bb,b) ->
      let vars = merge va vb in
      Open(vars, [], mk_apply2 f (snd (select va ba a)) (snd (select vb bb b)))

let unit_apply3 f t t' t'' = apply (unit_apply2 f t t') t''

let build_pair x y = unit_apply2 (fun x y -> x,y) x y

let build_list l =
  List.fold_right 
    (fun x l -> unit_apply2 (fun x l -> x::l) x l)
    l 
    (unit []) 

(* this one is a bit tricky because of the imperative nature of arrays *)
let mk_array t v = Array.of_list (t v)
let build_array a =
  let rec fold_array fn a i a' =
    if i < Array.length a then 
      fn a.(i) i (fold_array fn a (i+1) a')
    else
      a'
  in
  match 
    fold_array
      (fun x i a' -> unit_apply2 (fun x a' -> x::a') x a')
      a 0 (unit [])
  with
    Closed t -> Closed (Array.of_list t)
  | Open(vt,bt,t) -> 
      Open(vt,bt,mk_array t)

