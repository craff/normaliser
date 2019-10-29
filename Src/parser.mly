%{
open Lambda
open Parser_tool
open Action

let is_int str =
  try for i = 0 to String.length str - 1 do
    let c = Char.code str.[i] in
    if c < Char.code '0' || c > Char.code '9' then
      raise Exit
  done;
  true
  with Exit -> false

let check_dbl f l =
  let s = StringSet.empty in
  ignore (List.fold_left (fun s x ->
    let i,x = f x in
    if StringSet.mem x s then raise (Syntax_error (i, x^" is bound twice."));
    StringSet.add x s) s l)

%}

%token <info> Bslash Lparen Rparen Lbrack Rbrack Question Equal Semicol Rec Untyped
%token <info> Col Dot Star Exclam Forall Arrow Comma Let Redef And In Fun Exists
%token <info> Case Of Lbrace Rbrace
%token On Off Type Doquit Include Path Print Prrec Dotrace Domode Eof
%token <mode> Mode
%token <bool ref> Toggle
%token <info * string> Ident String
%token <string> Param
%start cmd
%nonassoc Forall Exists
%right Arrow
%type <bool> recs
%type <info * pkind> kind
%type <pkind list> kind_list
%type <(info * string) list> ikind_list arg_kind
%type <info * pterme> terme terme_atom terme_ass
%type <(info * pkind) obj> ass
%type <(info * string * pkind obj) list> ident_list ident_list_aux
%type <(info * string * pterme * pkind obj) list> terme_let let_suit terme_let_aux
%type <unit> cmd
%type <(string * pterme) list> rec_list case_list
%%

kind_list :
  kind
    { [snd $1] }
| kind Comma kind_list
    { snd $1::$3 }
;

ikind_list :
  Ident
    { [$1] }
| Ident Comma ikind_list
    { $1::$3 }
;

arg_kind :
  { [] }
| Lbrack ikind_list Rbrack
  { check_dbl (fun x -> x) $2; $2 }
;

kind_rec_list :
  { [] }
| kind_rec_list Ident Col kind Semicol
  { (snd $2, snd $4) :: $1 }

kind_case_list :
  { [] }
| kind_case_list Ident Col kind Semicol
  { (snd $2, snd $4) :: $1 }
| kind_case_list Ident Semicol
  { (snd $2, PPro (fst $2, [])) :: $1 }

kind_atom :
  Ident
    { let i,s = $1 in i, PTDef(i,s,[])}
| Ident Lbrack kind_list Rbrack
    { let i,s = $1 and l = $3 in
      let i = merge_info i $4 in i, PTDef(i,s,l) }
| Lparen kind Rparen
	{ $2 }
| Lbrack kind_case_list Rbrack
	    { let i = merge_info $1 $3 in
	      i, PSum(i, List.rev $2) }
| Lbrace kind_rec_list Rbrace
	    { let i = merge_info $1 $3 in
	      i, PPro(i, List.rev $2) }
| Question
    { $1, PUvr $1 }
| Forall Ident kind_atom
    { let _,s = $2 and i',k = $3 in
      let i = merge_info $1 i' in i, PForall(i,s,k) }
| Exists Ident kind_atom
    { let _,s = $2 and i',k = $3 in
      let i = merge_info $1 i' in i, PExists(i,s,k) }
| Exclam Ident kind_atom
    { if not !inductive then
        raise (Syntax_error($1,"Inductive types are illegal"));
      let i0,s = $2 and i',k = $3 in
      let i = merge_info $1 i' in i, PMu(i,s,k) }
| Question Ident kind_atom
    { if not !inductive then
        raise (Syntax_error($1,"Inductive types are illegal"));
      let i0,s = $2 and i',k = $3 in
      let i = merge_info $1 i' in i, PNu(i,s,k) }
;

kind :
  kind_atom
    { $1 }
| kind Arrow kind
    { let i,k = $1 and i',k' = $3 in
      let i = merge_info i i' in i, PArrow(i,k,k') }
;

ass :
  Col kind
    { Something $2 }
|   { Nothing }
;

ident_list_aux :
  Ident ass
    { let i,s = $1 in
      let i,k = merge_info_ass i $2 in [i,s,k] }
| Ident ass ident_list_aux
    { let i,s = $1 and l = $3 in
      let i,k = merge_info_ass i $2 in ((i,s,k)::l) }
;

ident_list :
 ident_list_aux
   { check_dbl (fun (i,x,_) -> i,x) $1; $1 }
;

lambda :
  Bslash {$1}
| Fun    {$1}
;

case_list :
    { [] }

| case_list Ident Lbrack Rbrack Arrow terme Semicol
    { let i,name = $2 in
      let i'' = merge_info $3 $4 in
      let i', t = $6 in
      let i = merge_info i i' in
	  (name, PAbs(i, i'', "_", Nothing, t))::$1 }

| case_list Ident Lbrack Ident Rbrack Arrow terme Semicol
    { let i,name = $2 in
      let i', t = $7 in
      let i = merge_info i i' in
      (name, PAbs(i, fst $4, snd $4, Nothing, t))::$1 }

rec_list :
    { [] }
| rec_list Ident Equal terme Semicol
    { (snd $2, snd $4)::$1 }

terme_atom :
  Ident
    { let i,s = $1 in i, PVar(i, s) }
| Forall Ident terme
    { let _,s = $2 and i',t = $3 in
      let i = merge_info $1 i' in i, PLam(i,s,t) }
| terme_atom Col kind
    { let i,t = $1 and i',k = $3 in
      let i = merge_info i i' in i, PAss(i,t,k) }
| String
    { let i,s = $1 in i, PSide(i, s) }
| lambda ident_list Dot terme
    { let l = $2 and i',t = $4 in
      let i = merge_info $1 i' in i,
        List.fold_right (fun (i',s,k) t -> PAbs(i,i',s,k,t)) l t }
| Ident Lbrack terme Rbrack
	{ let i, name = $1 in
	  let i = merge_info i $4 in
  (i, PCstr(i,name,snd $3)) }
| Ident Lbrack Rbrack
	{ let i, name = $1 in
	  let i = merge_info i $3 in
  (i, PCstr(i,name,PRec(merge_info $2 $3, []))) }
| Case terme Of Lbrack case_list Rbrack
	    { let i = merge_info $1 $6 in
	      (i, PCase(i, snd $2, List.rev $5)) }

| Lbrace rec_list Rbrace
 	    { let i = merge_info $1 $3 in
	      (i, PRec(i, List.rev $2)) }

| Let recs terme_let In terme
    { let ll = $3 and i,t = $5 in
      let size = 1 + List.length ll in
      let v = Array.make size t and sl = Array.make size (i,"") in
      let rec fn i = function
        [] -> ()
      | (i',s,t,k)::ll -> v.(i) <- t; sl.(i) <- i',s; fn (i+1) ll in
      fn 1 ll;
      let i = merge_info $1 i in
      i, PLet(i,$2,sl,v) }
| Lparen terme Rparen
    { $2 }
;

terme_ass :
  terme_atom
    { $1 }
| terme_ass Col kind
    { let i,t = $1 and i',k = $3 in
      let i = merge_info i i' in i, PAss(i,t,k) }
| terme_ass Dot Ident
	{ let i,t = $1 and i',name = $3 in
	  let i = merge_info i i' in i, PProj(i,t,name) }
;

terme :
  terme_ass
    { $1 }
| terme terme_ass
    { let i,t = $1 and i',t' = $2 in
      let i = merge_info i i' in i, PApp(i,t,t') }
;

terme_let_aux :
  ident_list Equal terme let_suit
    { let l = $1 and i',t = $3 and ll = $4 in
      match l with
        [] -> failwith "bug in parsing let"
      | (i,s,k)::l ->
          let i = merge_info i i' in
          let t = List.fold_right (fun (i',s,k) t -> PAbs(i,i',s,k,t)) l t in
          let t = match k with
            Nothing -> t
          | Something k -> PAss(i,t,k) in
          (i,s,t,k)::ll}
;

let_suit :
  And terme_let_aux
    { $2 }
|   { [] }
;

terme_let :
  terme_let_aux
    {  check_dbl (fun (i,x,_,_) -> i,x) $1; $1 }
;

state :
  On
    { true }
| Off
    { false }
|   { true }
;

recs :
  Rec
    {if !recursive <> true then
      raise (Syntax_error($1,"Illegal recursive definition."));
     true}
|   {false}

cmd :
  Let recs terme_let Semicol
    { action_let $1 $2 true $3 }
| Redef recs terme_let Semicol
    { action_let $1 $2 false $3 }
| terme Semicol
    { action_norm (snd $1) }
| Type Ident arg_kind Equal kind Semicol
    { action_type (snd $2) $3 (snd $5) }
| Untyped terme Semicol
    { action_untyped $1 (snd $2) }
| Toggle state Semicol
    { action_toggle $1 $2 }
| Param Semicol
    { action_print_param $1 }
| Param int Semicol
    { action_param $1 $2 }
| Doquit Semicol
    { raise Quit }
| Include String Semicol
    { action_include (snd $2) }
| Path String Semicol
    { action_path (snd $2) }
| Path Semicol
    { action_print_path () }
| Domode Mode Semicol
    { action_mode $2 }
| Domode Dotrace Semicol
    { action_mode Trace }
| Domode Semicol
    { action_print_mode () }
| Print terme Semicol
    { action_print (snd $2) }
| Prrec terme Semicol
    { action_prrec (snd $2) }
| Dotrace Ident state Semicol
    { action_trace_one $2 (-1,$3) }
| Dotrace Ident int Semicol
    { action_trace_one $2 ($3,true) }
| Dotrace Semicol
    { action_print_trace () }
| Eof
    { pop_input () }
;

int :
  Ident
    { let n = snd $1 in
      if is_int n then (int_of_string n) else
      raise (Syntax_error (fst $1, "wait for integer")) }


%%
