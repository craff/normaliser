open Format;;
open Bindlib;;
open Lambda;;
open Sys;;
open Filename;;

exception Quit;;
exception Syntax_error of info * string;;

type pCell =
    Dir of kind pre_term
  | Arg of int * kind array pre_term
;;

type pkind =
    PForall of info * string * pkind
  | PMu of info * string * pkind
  | PExists of info * string * pkind
  | PNu of info * string * pkind
  | PArrow of info * pkind * pkind
  | PTDef of info * string * pkind list
  | PSum of info * (string * pkind) list
  | PPro of info * (string * pkind) list
  | PUvr of info
;;

type pterme =
    PAbs of info * info * string * pkind obj * pterme
  | PAss of info * pterme * pkind
  | PLam of info * string * pterme
  | PApp of info * pterme * pterme
  | PVar of info * string
  | PLet of info * bool * (info * string) array * pterme array
  | PSide of info * string
  | PCstr of info * string * pterme
  | PProj of info * pterme * string
  | PCase of info * pterme * (string * pterme) list
  | PRec of  info * (string * pterme) list
;;

let merge_info
  {lbg=lbg1; cbg=cbg1; lnd=lnd1; cnd=cnd1}
  {lbg=lbg2; cbg=cbg2; lnd=lnd2; cnd=cnd2} =
    let lbg,cbg =
	  if lbg1 < lbg2 then lbg1, cbg1
	  else if lbg1 > lbg2 then lbg2, cbg2
	  else lbg1, min cbg1 cbg2 in
    let lnd,cnd =
	  if lnd1 > lnd2 then lnd1, cnd1
	  else if lnd1 < lnd2 then lnd2, cnd2
	  else lnd1, max cnd1 cnd2 in
  {lbg=lbg; cbg=cbg; lnd=lnd; cnd=cnd}
;;

let merge_info_ass i = function
  Nothing -> i, Nothing
| Something (i',k) -> merge_info i i', Something k
;;

let rec pkind2kind ltenv = function
      PTDef (i,s,l) -> (
        try
          let r = List.assoc s ltenv in
          if l <> [] then
            raise (Syntax_error (i,"local variable with arguments: "^s));
          match r with Dir k -> k | Arg (n,v) -> bproj n v
        with Not_found ->
        try
	  bTDef (Hashtbl.find tenv s) (Array.of_list
					 (List.map (pkind2kind ltenv) l))
        with Not_found ->
          raise (Syntax_error (i,"unbound: "^s)))
    | PForall(_,s,k) ->
         bForall s (fun x -> pkind2kind ((s,Dir x)::ltenv) k)
    | PMu(_,s,k) ->
         bMu s (fun x -> pkind2kind ((s,Dir x)::ltenv) k)
    | PExists(_,s,k) ->
         bExists s (fun x -> pkind2kind ((s,Dir x)::ltenv) k)
    | PNu(_,s,k) ->
         bNu s (fun x -> pkind2kind ((s,Dir x)::ltenv) k)
    | PArrow(_,k,k') ->
         let k = pkind2kind ltenv k in
         let k' = pkind2kind ltenv k' in
         bArrow k k'
    | PSum(i,l) -> bSum  (List.map (fun (s,t) -> (s, pkind2kind ltenv t)) l)
    | PPro(i,l) -> bPro  (List.map (fun (s,t) -> (s, pkind2kind ltenv t)) l)
    | PUvr _ -> bTUvr(new_uvr())
;;

let pobj2obj ltenv = function
  Nothing -> unit Nothing
| Something k -> unit_apply (fun x -> Something x) (pkind2kind ltenv k)
;;

let rec pterme2terme lenv ltenv = function
      PVar (i,s) -> (
        try
	  bIVar i (List.assoc s lenv ())
        with Not_found ->
        try
	  bFVar i (Hashtbl.find env s)
        with Not_found ->
	  raise (Syntax_error (i,"unbound: "^s)))
    | PAbs (i,i',s,k,t) ->
        bAbs i i' s
          (pobj2obj ltenv k)
          (fun x -> pterme2terme ((s,fun () -> x)::lenv) ltenv t)
    | PApp (i,t1,t2) ->
        let t1 = pterme2terme lenv ltenv t1 in
        let t2 = pterme2terme lenv ltenv t2 in
        bApp i t1 t2
    | PAss (i,t1,t2) ->
        let t1 = pterme2terme lenv ltenv t1 in
        let t2 = pkind2kind ltenv t2 in
        bAss i t1 t2
    | PLam(i,s,t) ->
       bLam i s (fun x -> pterme2terme lenv ((s, Dir x)::ltenv) t)
    | PCstr(i,s,t) -> bCstr i s (pterme2terme lenv ltenv t)
    | PProj(i,t,s) -> bApp i (pterme2terme lenv ltenv t) (bProj i s)
    | PCase(i,t,l) -> bApp i (pterme2terme lenv ltenv t) (bCase i (List.map (fun (s,t) -> (s, pterme2terme lenv ltenv t)) l))
    | PRec(i,l) -> bRec i (List.map (fun (s,t) -> (s, pterme2terme lenv ltenv t)) l)
    | PLet(i,b,sl,v) ->
         bLet i b sl
            (fun x ->
               let nenv = ref lenv in
               let size = Array.length sl in
               for i = 1 to size - 1 do
                 nenv:=(snd sl.(i), fun () -> bproj i x)::!nenv
               done;
               let r = Array.make size (unit (SVar "")) in
               for i = 1 to size - 1 do
                 r.(i) <-
                   pterme2terme (if b then !nenv else lenv) ltenv v.(i)
               done;
               r.(0) <- pterme2terme !nenv ltenv v.(0);
               r)
    | PSide (i,s) -> bSide i s
;;

let finalise t = start_term (pterme2terme [] [] t);;


let cur_input = ref stdin;;
let cur_name = ref "Input from terminal";;
let cur_line = ref 1;;
let cur_col = ref 0;;
let pv_col = ref (-1);;
let pv_lin = ref (-1);;

let stack_input = ref ([]:(in_channel * int * int * string) list);;

let test_console () = !stack_input = []

let start_new = ref true;;

let pop_input0 = function
    (c,l,r,n)::s ->
        print_string "Closing file \"";
        print_string !cur_name;
        print_endline "\".";
        start_new:=true;
        close_in !cur_input;
        cur_input := c;
        cur_name := n;
        cur_line := l;
        cur_col := r;
        pv_col := r;
        pv_lin := l;
        stack_input := s
|    [] ->
        raise Quit
;;

let pop_input () = pop_input0 !stack_input;;
let pop_all () = while not (test_console ()) do pop_input () done;;

let path = ref ([] : string list);;

let open_path filename =
  try open_in filename
  with Sys_error _ as error ->
    if not (is_implicit filename) then raise error
    else
      let rec fn = function
	    [] -> raise error
	   | dir::l -> try open_in (concat dir filename)
	               with Sys_error _ -> fn l
      in fn !path
;;

let read_file filename =
    let oin = !cur_input in
    cur_input := (open_path filename);
    stack_input := (oin,!cur_line,!cur_col,!cur_name)::!stack_input;
    pv_col := 0;
    pv_lin := 0;
    cur_line := 1;
    cur_col := 0;
    cur_name := filename;
    print_string "Opening file \"";
    print_string !cur_name;
    print_endline "\"."
;;

let prompt = "%> ";;

let print_prompt() =
  print_string prompt; print_flush ()
;;

let init = ref true;;

let bol = ref true;;

let isize = ref 1023;;
let ibuf = ref (Bytes.make 1024 ' ');;
let icur = ref 0;;
let ilin = ref 0;;
let icol = ref 0;;

let replace_string dest src pos =
  if pos < 0 || pos + Bytes.length src > Bytes.length dest
  then invalid_arg "replace_string"
  else Bytes.blit src 0 dest pos (Bytes.length src)
;;

let rec read_fun str pos =
  try
    if !bol && test_console () then print_prompt();
    let c = input_char !cur_input in
    pv_col:=!cur_col;
    pv_lin:=!cur_line;
    if !start_new then begin
      icur:=0; icol:=!cur_col; ilin:=!cur_line
    end;
    if !icur < !isize then
      Bytes.set !ibuf !icur c
    else begin
      let old = !ibuf in
      isize:=2 * !isize + 1;
      ibuf := Bytes.make (!isize+1) ' ';
      replace_string !ibuf old 0;
      Bytes.set !ibuf !icur c
    end;
    incr icur;
    incr cur_col;

    start_new:= c == ';';
    bol := c == '\n';
    if !bol then begin incr cur_line; cur_col := 0 end;
    if c == '\013' then cur_col := 0;
    Bytes.set str 0 c;
    1

  with End_of_file ->
    bol := !init;
    init:= false;
    Bytes.set !ibuf !icur (Char.chr 0xFF);
    0
;;

let is_end_of_file () = Bytes.get !ibuf !icur = Char.chr (0xFF);;

let print_input {lbg=lbg; cbg=cbg; lnd=lnd; cnd=cnd} =
  Bytes.set !ibuf !icur '\n';
  let cl = ref !ilin and cc = ref !icol and ic = ref 0 in
  while !cl < lbg do
    let c = Bytes.get !ibuf !ic in
    incr ic;
    if c = '\n' then (incr cl; cc := 0) else incr cc
  done;
  while !cl <= lnd do
    let ic' = ref !ic in
    (try while true do
      let c = Bytes.get !ibuf !ic' in
      incr ic';
      print_char c;
      if c == ';' then print_char '\n';
      if c == '\n' || c == ';' then raise Exit
    done with Exit -> ());
    (try while true do
      let c = Bytes.get !ibuf !ic in
      incr ic;
      incr cc;
      if (lbg < !cl && !cl < lnd) ||
         (lbg = !cl && !cl < lnd && cbg <= !cc) ||
         (lnd = !cl && lbg < !cl && cnd >= !cc) ||
         (lnd = !cl && lbg = !cl && cbg <= !cc && cnd >= !cc)
      then print_char '^' else print_char ' ';
      if c == '\n' || c == ';' then (print_char '\n'; raise Exit)
    done with Exit -> ());
    cc:=0; incr cl
  done
;;

(*
(**) #open "profile";;
let finalise = profile "finalise" finalise;;
(* let read_fun = profile2 "read_fun" read_fun;; *)
*)
