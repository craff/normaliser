(* action prour le parser *)

open Format;;
open Bindlib;;
open Lambda;;
open Parser_tool;;
open Typing;;

let dummy = SVar "";;
let new_valeur s = {name = s; valeur = dummy; trace = false; ttype = Nothing;
                    nbargs = -1; islam = false; old = false; cterme = CSVar ""}
;;

let islam = function
  FVar (_,v) -> v.islam
| Abs (_,_,_,_,_) -> true
| _ -> false
;;

let action_let i recs static l =
if (not (!recursive)) && recs then raise
  (Syntax_error(i,"Illegal recursive definition."));
let l' = List.map (function (_,s,_,_) ->
  try
    let ov = Hashtbl.find env s in
    if static then begin
      Hashtbl.remove env s;
      let v = new_valeur s in
      if recs then Hashtbl.add env s v;
      v, ov, true
    end else begin
      if (not (recs)) then Hashtbl.remove env s;
      ov, ov, true
    end
  with Not_found ->
    let v = new_valeur s in
    if recs then Hashtbl.add env s v;
    v, v, false) l
in
  let l = List.map (fun (_,s,t,_) -> (s, finalise t)) l in
try
  List.iter2 (fun (v,ov,b) (s,t) ->
    if b && static then ov.old <- true;
    if (not (recs)) then Hashtbl.add env s v;
    if b && static then begin
      print_string "Warning: hiding old definition of \"";
      print_string v.name;
      print_endline "\"."
    end else if b then begin
      print_string "Warning: redefinition of \""; print_string v.name;
      print_endline "\"."
    end else if (not (!typed)) then begin
      print_string "New term \""; print_string v.name;
      print_endline "\" defined."
    end;
    v.valeur <- t;
    v.ttype <- if !typed then Something (TUvr(new_uvr())) else Nothing;
    v.cterme <- terme2cterme t;
    v.islam <- islam t) l' l;
  if !typed then List.iter (fun (v,ov,_) ->
    let k = type_chck v.valeur v.ttype in
    print_string v.name;
    print_string " : ";
    print_ckind k;
    print_newline ();
    if (not (static)) then begin
      match ov.ttype with
        Nothing -> failwith
          ("Old version of "^ov.name^
          " was untyped, it can not be redefined with a typed term.")
      | Something k' ->
          try equal k k'
          with Subtype_fail _ -> failwith
          ("Old version of "^ov.name^
           " had another type, it can not be redefined.")
    end;
    v.ttype <- Something k) l'
with e ->
  List.iter2 (fun (v,ov,b) (s,_) ->
    if ((not (b)) || static) && recs then
      Hashtbl.remove env s;
    if b && (static || (not (recs))) then
      Hashtbl.add env v.name ov) l' l;
  raise e
;;

let action_type s l t =
  let k = start_term (bind (fun x ->
    let l, _= List.fold_left (fun (l,n) (_,s) -> ((s, Arg(n,x))::l), n+1)
      ([],0) l in
    pkind2kind l t)) in
    let n = List.length l in
    let td = {name_tdef = s; arity_tdef = n; val_tdef = k;
              occur_tdef = build_sign n k; old_tdef = false} in
      (try
        ignore (Hashtbl.find tenv s);
        Hashtbl.remove tenv s;
        print_string "Warning hiding old type "; print_string s;
        print_endline "."
      with Not_found ->
        print_string "New type "; print_string s;
        print_endline " defined.");
      Hashtbl.add tenv s td
;;

exception Wrong_untyped of info

let action_untyped i t =
  try
    let t = finalise t in
    if !typed then ignore (type_inf t);
    raise (Wrong_untyped i)
  with
    Type_error _ -> ()
;;

let action_toggle toggle state =
  print_toggle toggle;
  toggle:=state;
  if state then begin
    print_endline " is now on."
  end else begin
    print_endline " is now off."
  end
;;

let action_print_param s =
  print_string s;
  print_string " = ";
  print_int (snd (List.assoc s params) ());
  print_newline ()
;;

let action_param s v =
  fst (List.assoc s params) v;
  print_string s;
  print_string " = ";
  print_int (snd (List.assoc s params) ());
  print_newline ()
;;

let action_include name =
  try read_file name
  with
    Sys_error _ ->
      failwith ("Impossible to open file \""^name^"\".")
;;

let action_path name =
  if (not ((List.mem name !path))) then path:= name::!path;
  print_string "\"";
  print_string name;
  print_endline "\" added to the path-list"
;;

let action_print_path () =
  print_endline "The path-list is:";
  List.iter (fun s -> print_string "    ";
    print_endline s) !path
;;

let action_mode = function
  Lazy ->
    mode:=Lazy;
    print_endline "Evaluation mode changed to \"lazy\"."
| Left ->
    mode:=Left;
    print_endline "Evaluation mode changed to \"left\"."
| Trace ->
    mode:=Trace;
    print_endline "Evaluation mode changed to \"trace\"."
;;

let action_print_mode () =
  match !mode with
    Left -> print_endline "Evaluation mode is \"left\"."
  | Lazy -> print_endline "Evaluation mode is \"lazy\"."
  | Trace -> print_endline "Evaluation mode is \"trace\"."
;;

let action_print t =
  let rec fn = function
    FVar (_,v) -> fn (v.valeur)
  | t -> t
  in print_terme (fn (finalise t));
  print_newline ()
;;

let action_prrec t =
  prrec_terme (finalise t);
  print_newline ()
;;

let action_trace_one (i,s) (nb_args,state) =
  try
    let v = Hashtbl.find env s in
    print_string "\"";
    print_string s;
    if (not (state)) then begin
      print_endline "\" is no longer traced.";
      v.trace <- false
    end else begin
      print_string "\" is now traced";
      if nb_args > 0 then begin
        print_string " (at most ";
        print_int nb_args;
        if nb_args > 1 then
          print_endline " arguments are printed)."
        else
          print_endline " argument is printed)."
      end else print_endline ".";
      v.trace <- true;
      v.nbargs <- nb_args
    end
  with Not_found -> raise (Syntax_error (i,"unbound: "^s))
;;

let action_print_trace () =
    let l = ref [] in
    Hashtbl.iter (fun _ v -> if v.trace then l:=v::!l) env;
    if l = ref [] then
      print_endline "No term are traced"
    else begin
      if List.length !l = 1 then
        print_endline "The following term is traced:"
      else
        print_endline "The following terms are traced:";
      List.iter (fun v ->
        print_string "    ";
        print_string v.name;
        if v.nbargs > 0 then begin
          print_string " (at most ";
          print_int v.nbargs;
          if v.nbargs > 1 then
            print_endline " arguments are printed)."
          else
            print_endline " argument is printed)."
          end else print_newline ()
        ) !l
    end
;;

let action_norm t =
  let t = finalise t in
  open_hovbox 0;
  if !typed then (
    let k = type_inf t in
    print_string "_ ";
    print_string ": ";
    print_ckind k;
    print_space ())
  else (
    print_string "_ "
  );
  print_string "="; print_space ();
  norm (terme2cterme t);
  close_box ()
;;

(*
(**) #open "profile";;
let action_let = profile4 "action_let" action_let;;
let action_type = profile3 "action_type" action_type;;
*)
