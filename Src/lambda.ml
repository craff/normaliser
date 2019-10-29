open Bindlib;;
open Format;;

type info = {lbg:int; cbg:int; lnd:int; cnd:int};;

type  'a obj =
  Nothing
| Something of 'a
;;

module IntOrd = struct
  type t = int
  let compare = compare
end
module StringOrd = struct
  type t = string
  let compare = compare
end
module IntSet = Set.Make (IntOrd)
module StringMap = Map.Make (StringOrd)
module StringSet = Set.Make (StringOrd)

type occur = None0 | Pos | Neg | Both;;

type kind =
  Forall of string * (kind, kind) binder
| Mu of string * (kind, kind) binder
| Exists of string * (kind, kind) binder
| Nu of string * (kind, kind) binder
| Arrow of kind * kind
| Pro of (string * kind) list
| TDef of tdef * kind array
| TCst of int ref
| MCst of int * (kind -> kind)
| NCst of int * (kind -> kind)
| TUvr of var_cell
| TStr of string
| TTVar of kind pre_term

and var_cell = {uvr_key : int; mutable uvr_val : kind obj;
                               mutable uvr_eig : IntSet.t}

and tdef = {name_tdef : string; arity_tdef : int; old_tdef : bool;
            occur_tdef : occur array; val_tdef : (kind array,kind) binder}
;;

(* type des termes *)
type terme =
(* atomes auxilliares (non utilises dans un vrai terme) *)
    SVar of string
  | TVar of terme pre_term
  | TCVar of (unit -> cterme pre_term)
  | TKVar of (info * string * kind)
  | Kpi of terme list
(* les vrais constructeurs *)
  | IVar of info * terme
  | Side of info * string
  | FVar of info * valeur
  | Abs of info * info * string * kind obj * (terme,terme) binder
  | App of info * terme * terme
  | Lam of info * string * (kind, terme) binder
  | Ass of info * terme * kind
  | Let of info * bool * (info * string) array *
           (terme array, terme array) binder
  | Cc
  | Cstr of info * string * terme (* just an optimisation for (\lambda x (x.l t)) *)
  | Proj of info * string
  | Rec of info * (string * terme) list

and valeur = {name:string; mutable valeur: terme; mutable ttype :
              kind obj; mutable trace : bool; mutable nbargs : int;
              mutable islam : bool; mutable old : bool;
              mutable cterme : cterme}

and cterme =
(* atomes auxilliares (non utilises dans un vrai terme) *)
    CSVar of string
  | CTVar of string * cterme pre_term
  | CBox of (bool * cterme) ref
  | CUBox of cterme (* only a box in there *)
  | CKpi of cterme list
(* les vrais constructeurs *)
  | CSide of string
  | CFVar of valeur
  | CAbs of string * (cterme,cterme) binder
  | CApp of cterme * cterme
  | CLet of bool * (info * string) array * (cterme array, cterme array) binder
  | CCstr of string * cterme
  | CProj of string
  | CRec of (string * cterme) list
  | CCc
;;

type env_table = (string, valeur) Hashtbl.t;;
type tenv_table = (string, tdef) Hashtbl.t;;

type mode = Left | Lazy | Trace;;

set_ellipsis_text "...";;
set_max_indent 40;;
let print_newline = force_newline;;
let print_endline s = print_string s; force_newline ();;
let tab = ref 2;;

let bproj n args = unit_apply (fun v -> v.(n)) args;;
let bMu s f = unit_apply (fun x -> Mu(s,x)) (bind f);;
let bForall s f = unit_apply (fun x -> Forall(s,x)) (bind f);;
let bNu s f = unit_apply (fun x -> Nu(s,x)) (bind f);;
let bExists s f = unit_apply (fun x -> Exists(s,x)) (bind f);;
let bArrow = unit_apply2 (fun x y -> Arrow(x,y));;
let bPro l = unit_apply (fun l -> Pro(l)) (build_list (List.map (fun (s,t) -> build_pair (unit s) t) l))
let bTDef td l = unit_apply (fun l -> TDef(td,l)) (build_array l);;
let bTCst n = unit (TCst (ref n));;
let bTUvr v = unit (TUvr v);;

let bSum l = bForall "X" (fun x -> bArrow (bPro (List.map (fun (s,t) -> (s, bArrow t x)) l)) x)
let bCc = unit Cc
let bApp i = unit_apply2 (fun x y -> App(i,x,y));;
let bAbs i i' s t f = unit_apply2 (fun t x -> Abs(i,i',s,t,x)) t (bind f);;
let bLet i b vs v = unit_apply (fun v -> Let(i,b,vs,v))
  (bind (fun x -> build_array (v x)));;
let bProj i s = unit (Proj(i,s))
let bCstr i s t = unit_apply (fun t -> Cstr(i,s,t)) t
let bRec i l = unit_apply (fun l -> Rec(i,l)) (build_list (List.map (fun (s,t) -> build_pair (unit s) t) l))
let bSide i s = unit (Side (i,s));;
let bFVar i v = unit (FVar (i,v));;
let bLam i s f = unit_apply (fun x -> Lam(i,s,x)) (bind f);;
let bAss i = unit_apply2 (fun x y -> Ass(i,x,y));;
let bIVar i = unit_apply (fun y -> IVar(i,y));;
let bCase = bRec
let bCCc = unit CCc
let bCApp = unit_apply2 (fun x y -> CApp(x,y));;
let bCAbs s f = unit_apply (fun x -> CAbs(s,x)) (bind f);;
let bCLet b vs v = unit_apply (fun v -> CLet(b,vs,v))
                    (bind (fun x -> build_array (v x)));;
let bCSide s = unit (CSide (s));;
let bCFVar v = unit (CFVar (v));;
let bCProj s = unit (CProj s)
let bCCstr s t = unit_apply (fun t -> CCstr(s,t)) t
let bCRec l = unit_apply (fun l -> CRec(l)) (build_list (List.map (fun (s,t) -> build_pair (unit s) t) l))

let rec terme2cterme t=
  let rec fn = function
    TCVar x -> x ()
  | IVar(_,t) -> fn t
  | App(_,t1,t2) -> bCApp (fn t1) (fn t2)
  | Abs(_,_,s,_,f) ->
      bCAbs s (fun x -> fn (subst f (TCVar (fun () -> x))))
  | Side(_,s) -> bCSide s
  | FVar(_,v) -> bCFVar v
  | Let(_,b,sl,f) -> bCLet b sl (fun v ->
      let l = Array.length sl in
      let w = Array.make l (SVar "") in
      for i = 0 to l - 1 do w.(i) <- TCVar(fun () -> bproj i v) done;
      Array.map fn (subst f w))
  | Lam(_,_,f) -> fn (subst f (TStr ""))
  | Ass(_,t,_) -> fn t
  | Cc -> bCCc
  | Proj(i,s) -> bCProj s
  | Cstr(i,s,t) -> bCCstr s (fn t)
  | Rec(i,l) -> bCRec (List.map (fun (s,t) -> (s, fn t)) l)
  | SVar _|TVar _|TKVar _|Kpi _ -> failwith "bug in terme2cterme"
  in start_term (fn t)
;;

let verbose = ref false;;

let new_cst, reset_cst =
  let c = ref 0 in
  (fun () -> incr c; !c), (fun () -> c := 0)
;;

let new_uvr, reset_uvr =
  let c = ref 0 in
  (fun () -> incr c;
        {uvr_key = !c;
         uvr_val = Nothing;
         uvr_eig = IntSet.empty}),
  (fun () -> c := 0)
;;

let dum_kind = TStr "";;
let dum_terme = SVar "";;
let dum_cterme = CSVar "";;

let and_occur = fun
  p0 p1 -> match (p0,p1) with (None0, o) -> o
| (o, None0) -> o
| (Both, _) -> Both
| (_, Both) -> Both
| (Neg, Neg) -> Neg
| (Pos, Pos) -> Pos
| (_, _)     -> Both
;;

let not_occur = function
  None0 -> None0
| Both -> Both
| Pos -> Neg
| Neg -> Pos
;;

let build_sign n f =
  let v = Array.make n None0 in
  let w = Array.make n (TCst (ref (-1))) in
  for i = 0 to (n - 1) do w.(i) <- TCst (ref i) done;
  let rec fn pos = function
    Forall (_,f) | Mu (_,f)
  | Exists (_,f) | Nu (_,f) ->
      fn pos (subst f dum_kind)
  | Arrow(t,u) ->
      fn (not_occur pos) t; fn pos u
  | TDef(t,tl) ->
      for i = 0 to t.arity_tdef - 1 do
        if t.occur_tdef.(i) = None0 then () else fn t.occur_tdef.(i) tl.(i)
      done
  | TCst n -> v.(!n) <- and_occur pos v.(!n)
  | TStr _ -> ()
  | Pro l -> List.iter (fun (_,t) -> fn pos t) l
  | MCst (_, _)|NCst (_, _)|TUvr _|TTVar _ -> failwith "bug in build_sign"
  in fn Pos (subst f w); v
;;


(* table des termes definis par let *)

let env = (Hashtbl.create 41 : env_table);;
let tenv = (Hashtbl.create 41 : tenv_table);;
let var_used = ref StringMap.empty;;

let split s =
  let i = ref 0 and p = ref (String.length s - 1) in
  while  !p >= 0 &&
         let code = Char.code (String.get s !p) in
           code >= Char.code '0' &&
           code <= Char.code '9' do
    i := 10 * !i + Char.code (String.get s !p) - Char.code '0'; decr p
  done;
  String.sub s 0 (!p+1), !i
;;

let get_fresh varl name =
  let root,index = split name in
  try
    let j = StringMap.find root varl in
    if j <= index then
      (StringMap.add root (index+1) varl), name
    else
      (StringMap.add root (j+1) varl), root^(string_of_int j)
  with Not_found ->
    StringMap.add root (index+1) varl, name
;;

let add_used name =
  let root,index = split name in
  let varl = !var_used in
  try
    let j = StringMap.find root varl in
    if j <= index then
      var_used:=StringMap.add root index varl
  with Not_found ->
    var_used:=StringMap.add root (index+1) varl
;;

let rec print_kind varl b = function
  Forall (s, f) ->
    let varl,s = get_fresh varl s in
    let t = subst f (TStr s) in
    print_string "/\\";
    print_string s;
(*    if l <> [] then begin
      print_string ">";
      let rec fn = function
        [t] -> print_kind varl false t
      | t::l -> print_kind varl false t; print_string ","; fn l
      | _ -> failwith "bug in print_kind"
      in fn l
    end;*)
    print_break (1,!tab);
    print_kind varl true t
  | Exists (s, f) ->
    let varl,s = get_fresh varl s in
    let t = subst f (TStr s) in
    print_string "\\/";
    print_string s;
(*    if l <> [] then begin
      print_string ">";
      let rec fn = function
        [t] -> print_kind varl false t
      | t::l -> print_kind varl false t; print_string ","; fn l
      | _ -> failwith "bug in print_kind"
      in fn l
    end;*)
    print_break (1,!tab);
    print_kind varl true t
| Mu (s, f) ->
    let varl,s = get_fresh varl s in
    print_string "!";
    print_string s;
    print_break (1,!tab);
    print_kind varl true (subst f (TStr s))
| Nu (s, f) ->
    let varl,s = get_fresh varl s in
    print_string "?";
    print_string s;
    print_break (1,!tab);
    print_kind varl true (subst f (TStr s))
| Arrow(t1,t2) ->
    if b then (open_hovbox 0; print_string "("; print_break (0,!tab));
    print_kind varl true t1;
    print_string " ->";
    print_break (1,!tab);
    print_kind varl false t2;
    if b then (print_hcut (); print_string ")"; close_box ())
| TDef(td,l) ->
    print_string td.name_tdef; if td.old_tdef then print_string "#old#";
    if l <> [||] then begin
      print_string "["; open_hovbox 0;
      for i = 0 to Array.length l - 1 do
        print_kind varl false l.(i);
        if i = Array.length l - 1 then (close_box (); print_string "]")
          else (print_string ",";print_break (0,!tab))
      done
    end
| Pro l ->
   print_string "{";
   open_hovbox 2;
   List.iter (function (s, t) ->
     print_string s; print_space (); print_string ":"; print_space (); print_kind varl false t; print_string ";"; print_space();) l;
   close_box ();
   print_string "}";

| TCst n -> print_string "!"; print_int (abs !n)
| MCst (n,_) -> print_string "!!"; print_int n
| NCst (n,_) -> print_string "!?"; print_int n
| TUvr{uvr_val = Nothing; uvr_key = k; uvr_eig = e} ->
    print_string "?"; print_int k;
    let first = ref true in
    IntSet.iter (fun n ->
		   if !first then print_string "{" else print_string " ";
		   first:=false;
		   print_int n; ) e;
    if not !first then  print_string "}"
| TUvr{uvr_val = Something t} -> print_kind varl b t
| TStr s -> print_string s
| TTVar _ -> print_string "#"

;;

let print_ckind t = open_hovbox 0; print_kind !var_used false t; close_box ()
;;

let print_terme, print_trace, prrec_terme =
    let prrec = ref false in
    let rec print_aux varl b = function
          SVar s -> print_string s
        | IVar(_,t) ->
            print_aux varl b t
        | TKVar (_,s,k) ->
            print_string s;
            print_string ":";
            print_break (0,!tab);
            open_hovbox 0;
            print_kind varl true k;
            close_box ()
        | Let (_,b,sl,fv) ->
            open_hvbox 0;
            let varl = ref varl in
            let args = Array.map (fun (i,s) ->
              let varl',s = get_fresh !varl s in
              varl := varl'; SVar s) sl in
            let v = subst fv args in
            for i = 1 to Array.length sl - 1 do
              if i = 1 then begin
                         print_string "let ";
                         if b then print_string "rec "
                       end else begin
                         print_break (1,0);
                         print_string "and "
                       end;
              print_aux !varl 0 args.(i);
              print_string " ="; print_break (1,!tab);
              open_hovbox 0;
              print_aux !varl 0 v.(i);
              close_box ()
            done;
            print_break (1,0);
            print_string "in ";
            open_hovbox 0;
            print_aux !varl 0 v.(0);
            close_box ();
            close_box ()
        | Side (_,s) -> print_string "\"";
                    print_string (String.escaped s);
                    print_string "\""
        | FVar (_,v) ->
            if !prrec then
              print_aux varl b v.valeur
            else
              print_string v.name; if v.old then print_string "#old#"
	| App(_,t,Proj(_,s)) -> print_aux varl 3 t; print_string "."; print_string s
        | App (_,t1,t2) ->
            if b > 1 then
              (open_hovbox 0; print_string "("; print_break (0,!tab));
            print_aux varl 1 t1;
            print_break (1,!tab);
            print_aux varl 2 t2;
            if b > 1 then (print_hcut (); print_string ")"; close_box ())
        | Ass (_,t,k) ->
            if b > 0 then
              (open_hovbox 0; print_string "("; print_break (0,!tab));
            print_aux varl 0 t;
            print_string ":";
            print_break (0,!tab);
            open_hovbox 0;
            print_kind varl true k;
            close_box ();
            if b > 0 then (print_hcut (); print_string ")"; close_box ())
        | Lam (_,s,f) ->
            if b > 0 then
              (open_hovbox 0; print_string "("; print_break (0,!tab));
            let varl,s = get_fresh varl s in
            let t = subst f (TStr s) in
            print_string "/\\";
            print_string "s";
            print_break (1,!tab);
            print_aux varl 0 t;
           if b > 0 then (print_hcut (); print_string ")"; close_box ())
        | Abs (_,_,s,t,f) ->
            let varl,s = get_fresh varl s in
            if b > 0 then
              (open_hovbox 0; print_string "("; print_break (0,!tab));
            print_string "\\";
            print_string s;
            (match t with
              Something t -> print_string ":"; print_kind varl true t
            | Nothing -> ());
            let rec fn varl = function
                  Abs (_,_,s,t,f) ->
                    let varl,s = get_fresh varl s in
                    print_string " ";
                    print_string s;
                    (match t with
                      Something t -> print_string ":"; print_kind varl true t
                    | Nothing -> ());
                    fn varl (subst f (SVar s))
                | t ->
                    print_string ".";
                    print_break (0,!tab);
                    print_aux varl 0 t in
            fn varl (subst f (SVar s));
            if b > 0 then (print_hcut (); print_string ")"; close_box ())
	| Cc -> print_string "Cc"
	| Cstr(_,s,t) -> print_string s; print_string "["; print_aux varl 0 t; print_string "]"
	| Rec(_,l) ->
	   print_string "{"; open_hovbox 2;
	   List.iter (fun (s,t) -> print_string s; print_space (); print_string "->"; print_space (); print_aux varl 0 t) l;
	   close_box (); print_string "}";
	| Proj (_, _)|TVar _|TCVar _|Kpi _ -> failwith "bug in print_terme"
    in
      (fun x -> prrec:=false; open_hovbox 0;
                print_aux !var_used 0 x; close_box ()),
      (fun x -> prrec:=false; open_hovbox 0;
                print_aux !var_used 2 x; close_box ()),
      (fun x -> prrec:=true; open_hovbox 0;
                print_aux !var_used 0 x; close_box ())
;;

let print_cterme, print_ctrace, prrec_cterme =
    let prrec = ref false in
    let rec print_aux varl b = function
          CSVar s -> print_string s
        | CTVar (s,_) -> print_string s
        | CBox ({contents = (_,t)}) -> print_aux varl b t
        | CLet (b,sl,fv) ->
            open_hvbox 0;
            let varl = ref varl in
            let args = Array.map (fun (_,s) ->
              let varl',s = get_fresh !varl s in
              varl := varl'; CSVar s) sl in
            let v = subst fv args in
            for i = 1 to Array.length sl - 1 do
              if i = 1 then begin
                print_string "let ";
                if b then print_string "rec "
              end else
                (print_break (1,0); print_string "and ");
              print_aux !varl 0 args.(i);
              print_string " ="; print_break (1,!tab);
              open_hovbox 0; print_aux !varl 0 v.(i); close_box ()
            done;
            print_break (1,0);
            print_string "in ";
            open_hovbox 0;
            print_aux !varl 0 v.(0);
            close_box ();
            close_box ()
        | CSide (s) ->
            print_string "\"";
            print_string (String.escaped s);
            print_string "\""
        | CFVar (v) ->
            if !prrec then
              print_aux varl b v.cterme
            else
              print_string v.name; if v.old then print_string "#old#"
	| CApp(t,CProj(s)) -> print_aux varl 3 t; print_string "."; print_string s
        | CApp (t1,t2) ->
            if b > 1 then
              (open_hovbox 0; print_string "("; print_break (0,!tab));
            print_aux varl 1 t1;
            print_break (1,!tab);
            print_aux varl 2 t2;
            if b > 1 then (print_hcut (); print_string ")"; close_box ())
        | CAbs (s,f) ->
            let varl,s = get_fresh varl s in
            if b > 0 then
              (open_hovbox 0; print_string "("; print_break (0,!tab));
            print_string "\\";
            print_string s;
            let rec fn varl = function
                  CAbs (s,f) ->
                    let varl,s = get_fresh varl s in
                    print_string " ";
                    print_string s;
                    fn varl (subst f (CSVar s))
                | t ->
                    print_string ".";
                    print_break (0,!tab);
                    print_aux varl 0 t in
            fn varl (subst f (CSVar s));
            if b > 0 then (print_hcut (); print_string ")"; close_box ())
	| CRec(l) ->
	   print_string "{"; open_hovbox 2;
	   List.iter (fun (s,t) -> print_string s; print_space (); print_string "="; print_space (); print_aux varl 0 t; print_string ";"; print_space();) l;
	   close_box (); print_string "}";
	| CCstr(s,t) -> print_string s; print_string "["; print_aux varl 0 t; print_string "]"
	| (CProj _|CUBox _|CKpi _|CCc) -> failwith "bug in print_terme"
    in
      (fun x -> prrec:=false;
                open_hovbox 0; print_aux !var_used 0 x; close_box ()),
      (fun x -> prrec:=false;
                open_hovbox 0; print_aux !var_used 2 x; close_box ()),
      (fun x -> prrec:=true;
                open_hovbox 0; print_aux !var_used 0 x; close_box ())
;;

let step = ref 0;;

(* un normalisateur en reduction gauche, avec une pile ...*)

let idt0 = start_term (bCAbs "x" (fun x -> x));;
let idt = start_term (bForall "X" (fun x -> x));;
let dum = CSVar "";;

let rec normg' t =
    let stack = ref [] in
    let rec norm_aux = function
          CTVar (_,x) -> do_app x
        | CFVar (v) ->
            if v.trace then begin
              print_endline " ....";
              close_box (); print_flush (); open_vbox 0;
              print_string "   ";
              print_string v.name;
              print_string " is applied to";
              let b = ref v.nbargs in
              if !stack = [] then print_endline " nothing." else begin
                print_endline ":";
                print_string "     ";
                open_vbox 0;
                (try List.iter (fun t ->
                  print_ctrace t;
                  print_newline ();
                  decr b; if !b = 0 then raise Exit) !stack
                with Exit -> ());
                close_box ();
                print_newline ()
              end
            end;
            norm_aux v.cterme
        | CSide (s) -> (
           print_string s;
           match !stack with
             [] -> do_app (unit idt0)
           | t::s -> stack:=s; incr step; norm_aux t)
        | CLet (_,sl,fv) ->
           let v = Array.make (Array.length sl) dum in
           for i = 0 to Array.length sl - 1 do
             v.(i) <- CBox(ref(false, dum))
           done;
           let v' = subst fv v in
           for i = 0 to Array.length sl - 1 do
             match v.(i) with
               CBox (ptr) -> ptr := false,v'.(i)
             | _ -> failwith "bug in normg"
           done;
           norm_aux v'.(0)
        | CBox({contents = (_,t)}) -> norm_aux t
        | CApp (t1,t2) ->
            stack:=t2::!stack;
            norm_aux t1
        | CAbs (s,f) -> (match !stack with
              [] -> bCAbs s (fun x -> norm_aux (subst f (CTVar (s,x))))
            | v::s -> stack:=s;incr step; norm_aux (subst f v))
	| CCstr(name,t) ->
	   (match !stack with
             [] -> bCCstr name (norm_aux t);
	   | CRec(l)::s ->
		let v = try List.assoc name l with Not_found -> failwith "bug in normg: missing case" in
		stack:=t::s;incr step; norm_aux v
	   | _::s -> failwith "bug in normg: non empty stack with Cstr")
	| CRec(l) ->
	   (match !stack with
             [] -> bCRec (List.map (fun (s,t) -> (s, norm_aux t)) l);
	   | CProj name::s ->
	      let v = try List.assoc name l with Not_found -> failwith "bug in normg: missing field" in
	      stack:=s;incr step; norm_aux v
	   | _::s -> failwith "bug in normg: non empty stack with CRec")
        | CCc -> (match !stack with
	      [] -> bCCc
            | v::s -> stack:=CKpi s::s;incr step; norm_aux v)
	| CKpi s -> (match !stack with
	  [] -> failwith "bug in normg: empty stack with kPi"
          | v::_ -> stack:=s; incr step; norm_aux v)
	| CSVar _|CUBox _|CProj _ -> failwith "bug in normg"
    and do_app x = (match !stack with
          [] -> x
        | v::s -> stack:=s;do_app (bCApp x (normg' v)))
    in norm_aux t
;;

let normg t = start_term (normg' t);;

(* un normalisateur lazy en reduction gauche, avec une pile ...*)

let rec norml' t =
    let stack = ref [] in
    let rec norm_aux = function
          CTVar (_,x) -> do_app x
        | CFVar (v) ->
            if v.trace then begin
              print_endline " ....";
              close_box (); print_flush (); open_vbox 0;
              print_string "   ";
              print_string v.name;
              print_string " is applied to";
              let b = ref v.nbargs in
              if List.for_all (function (CUBox _) -> true | _ -> false) !stack
                then print_endline " nothing." else begin
                print_endline ":";
                print_string "     ";
                open_vbox 0;
                (try List.iter (function (CUBox _) -> () | t ->
                  print_ctrace t;
                  print_newline ();
                  decr b; if !b = 0 then raise Exit) !stack
                with Exit -> ());
                close_box ();
                print_newline ()
              end
            end;
            norm_aux v.cterme
        | CSide (s) as t ->
           print_string s;
           let rec fn = function
             [] -> do_app (unit idt0)
           | (CUBox (CBox ptr))::s -> stack:=s; ptr := true, t; fn s
           | t::s -> stack:=s; incr step; norm_aux t
           in fn !stack
        | CLet (_,sl,fv) ->
           let v = Array.make (Array.length sl) (dum) in
           for i = 0 to Array.length sl - 1 do
             v.(i) <- CBox(ref(false, dum))
           done;
           let v' = subst fv v in
           for i = 0 to Array.length sl - 1 do
             match v.(i) with
               CBox ptr -> ptr :=  false,v'.(i)
             | _ -> failwith "bug in norml"
           done;
           norm_aux v'.(0)
        | CApp (t1,(CApp _ | CFVar {islam = false} as t2)) ->
            stack:=CBox(ref(false,t2))::!stack;
            norm_aux t1
        | CApp (t1,t2) ->
            stack:=t2::!stack;
            norm_aux t1
        | CBox({contents = (true,t1)}) ->
            norm_aux t1
        | CBox({contents = (false,t1)}) as t2 ->
            stack:=CUBox(t2)::!stack;
            norm_aux t1
        | CAbs (s,f) as t ->
            let rec fn = function
              [] -> bCAbs s (fun x -> norm_aux (subst f (CTVar (s,x))))
            | (CUBox(CBox ptr))::s ->
                 ptr:= (true, t);stack:=s;fn s
            | v::s -> stack:=s; incr step; norm_aux (subst f v)
            in fn !stack
	| CCstr(name,t) as u ->
            let rec fn = function
              | [] -> bCCstr name (norm_aux t);
              | (CUBox(CBox ptr))::s ->
                 ptr:= (true, u);stack:=s;fn s
	      | CRec(l)::s ->
		 let v = try List.assoc name l with Not_found -> failwith "bug in normg: missing case" in
		 stack:=t::s;incr step; norm_aux v
	      | v::s ->
		 stack:=CProj name :: t :: s; norm_aux v
	    in fn !stack
	| CRec(l) as u ->
            let rec fn = function
              | [] -> bCRec (List.map (fun (s,t) -> (s, norm_aux t)) l);
              | (CUBox(CBox ptr))::s ->
                 ptr:= (true, u);stack:=s;fn s
	      | CProj name::s ->
		 let v = try List.assoc name l with Not_found -> failwith "bug in normg: missing field" in
		 stack:=s;incr step; norm_aux v
	      | _::s -> failwith "bug in normg: non empty stack with Rec"
	    in fn !stack
        | CCc -> (match !stack with
	  [] -> bCCc
          | v::s -> stack:=CKpi s::s;incr step; norm_aux v)
	| CKpi s -> (match !stack with
	  [] -> failwith "bug in normg: empty stack with kPi"
          | v::_ -> stack:=s; incr step; norm_aux v)
        | _ -> failwith "bug in norml"
    and do_app t = (match !stack with
          [] -> t
        | (CUBox(CBox _))::s -> stack:=s;do_app t
        | v::s -> stack:=s;do_app (bCApp t (norml' v)))
    in norm_aux t
;;

let norml t = start_term (norml' t);;

(* un normalisateur "traceur" en reduction gauche, avec une pile ...*)

let rec normt t =
    let stack = ref [] in
    let dump = ref [] in
    let rec norm_aux varl n b =
       let rec do_app () = (match !stack with
               [] ->
                  (match !dump with
                    [] -> ()
                     | (b,s)::d ->
                     if b then print_string ")";
                     stack:= s; dump := d;
                     do_app ())
              | v::st ->
                  dump:=(b,st)::!dump;
                  stack:=[]; print_string " ";
                  norm_aux varl n true v)
        in function
          CSVar s ->
            if b && !stack <> [] then print_string "("; print_string s;
            do_app ()

        | CFVar (v) ->
            norm_aux varl n b v.cterme

        | CSide (s) -> (
           print_endline " .....";
           close_box (); print_flush (); open_vbox 0;
           print_string "    Side effect : ";
           print_endline s;
           match !stack with
             [] -> norm_aux varl n b idt0
           | t::s -> stack:=s; incr step; norm_aux varl n b t)

        | CLet (_,sl,fv) ->
           let v = Array.make (Array.length sl) (dum) in
           for i = 0 to Array.length sl - 1 do
             v.(i) <- CBox(ref(false, dum))
           done;
           let v' = subst fv v in
           for i = 0 to Array.length sl - 1 do
             match v.(i) with
               CBox ptr -> ptr := false,v'.(i)
             | _ -> failwith "bug in normt"
           done;
           norm_aux varl n b v'.(0)

        | CBox({contents = (_,t)}) ->
           norm_aux varl n b t

        | CApp (t1,t2) ->
            stack:=t2::!stack;
            norm_aux varl n b t1

        | CAbs (s,f) as t -> (match !stack with
            [] ->
              if b then print_string "(";
              print_string "\\";
              let varl, s = get_fresh varl s in
              print_string s;
              print_string ".";
              if b then dump:=(true,[])::!dump;
              norm_aux varl (succ n) false (subst f (CSVar s))
          | v::s ->
              print_string " ....."; close_box (); print_flush ();
              open_vbox 0;
              print_break (0,4);
              if b then print_string "(";
              print_ctrace t;
              List.iter (fun t ->
                print_break (0,8);
                print_ctrace t) !stack;
              if b then print_string ")";
              let rec print_dump = function
                [] -> ()
              | (b,s)::dp ->
                  if b then print_string ")";
                  if s <> [] then begin
                    print_break (0,4)
                  end;
                  open_hovbox 0;
                    List.iter (fun t ->
                      print_break (1,!tab);
                    print_ctrace t) s;
                  close_box ();
                  print_dump dp in
              print_dump !dump;
              print_newline ();
              print_newline ();
              stack:=s;incr step; norm_aux varl n b (subst f v))

	| CCstr(name,t) ->
	   (match !stack with
             [] -> norm_aux varl n b t;
	   | CRec(l)::s ->
		let v = try List.assoc name l with Not_found -> failwith "bug in normg: missing case" in
		stack:=t::s;incr step; norm_aux varl n b v
	   | _::s -> failwith "bug in normg: non empty stack with Cstr")
	| CRec(l) ->
	   (match !stack with
             [] -> List.iter (fun (s,t) -> norm_aux varl n b t) l;
	   | CProj name::s ->
	      let v = try List.assoc name l with Not_found -> failwith "bug in normg: missing field" in
	      stack:=s;incr step; norm_aux varl n b v
	   | _::s -> failwith "bug in normg: non empty stack with CRec")
        | CCc -> (match !stack with
	  [] -> ()
          | v::s -> stack:=CKpi s::s;incr step; norm_aux varl n b v)

	| CKpi s -> (match !stack with
	  [] -> failwith "bug in normg: empty stack with kPi"
          | v::_ -> stack:=s; incr step; norm_aux varl n b v)
        | _ -> failwith "bug in normt"
    in norm_aux !var_used 0 false t
;;


let mode = ref Lazy;;
let recursive = ref false;;
let typed = ref false;;
let verbose = ref false;;
let inductive = ref false;;

let print_toggle tgl =
  if tgl == recursive then print_string "recursive" else
  if tgl == typed then print_string "typed" else
  if tgl == verbose then print_string "verbose" else
  if tgl == inductive then print_string "inductive" else
  failwith "Unknown toggle"
;;

let params =
  ["margin", (set_margin, get_margin);
   "max_indent", (set_max_indent, get_max_indent);
   "max_depth", (set_max_boxes, get_max_boxes);
   "tab", ((fun n -> tab:=n),(fun () -> !tab))]
;;

let norm t =
  step := 0;
  (match !mode with
    Lazy -> print_cterme (norml t); print_newline ()
  | Left -> print_cterme (normg t); print_newline ()
  | Trace -> normt t; print_newline ());
  print_string "number of beta-reduction : ";
  print_int !step;
  print_newline ()
;;

(*
#open "profile";;
let print_ckind = profile "print_ckind" print_ckind;;
let print_terme = profile "print_terme" print_terme;;
let terme2cterme = profile "terme2cterme" terme2cterme;;
let build_sign = profile2 "build_sign" build_sign;;
*)
