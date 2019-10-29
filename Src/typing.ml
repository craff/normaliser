open Lambda;;
open Bindlib;;
open Format;;

exception Subtype_fail of string;;
exception Type_error of info * kind * kind;;

let rec normk = function
  TUvr ({uvr_val = v} as vc) as c -> (
    match v with
      Nothing -> c
    | Something c ->
        let c' = normk c in
        if c != c' then begin
	  vc.uvr_val <- Something c';
          c'
        end else c')
| t -> t
;;

let occur_prog {uvr_key = vkey; uvr_eig = eigs} c =
  let occur = ref None0 in
  let rec fn pos c =
  let t = normk c in
  match t with
  | Forall (_, f) | Exists(_, f)
  | Mu (_, f) | Nu(_, f) ->
      let t = subst f dum_kind in
      fn pos t
  | Arrow (t,t') ->
      fn (not_occur pos) t; fn pos t'
  | TStr n -> ()
  | TTVar _ -> failwith "bug in occur_prog"
  | TDef (t,tl) ->
      for i = 0 to t.arity_tdef - 1 do
        if t.occur_tdef.(i) = None0 then () else fn t.occur_tdef.(i) tl.(i)
      done
  | Pro l -> List.iter (fun (_, t) -> fn pos t) l
  | TCst { contents = n }  | MCst (n,_) | NCst(n,_) ->
      if IntSet.mem n eigs then begin
	if !verbose then begin
	  print_string "eigens failure for ";
	  print_int n;
	  print_newline ();
	end;
	raise (Subtype_fail "Eig failure")
      end
  | TUvr ({uvr_key = i; uvr_val = v; uvr_eig = e} as vc) ->
      if i = vkey then occur:=and_occur !occur pos;
      match v with
        Nothing ->
          let i = IntSet.diff eigs e in
          if (not (IntSet.is_empty i)) then begin
            vc.uvr_eig <- IntSet.union e i
          end
      | Something c ->
         failwith "bug in occur_prog"
  in fn Pos c; !occur
;;

let add_cst n gamma =
  let v = {uvr_key = -1;
           uvr_val = Nothing;
           uvr_eig = IntSet.add n IntSet.empty}
  in
    List.iter (fun x -> ignore (occur_prog v x)) gamma
;;

let capture_var cv c x =
  let rec fn c =
    let t = normk c in
    match t with
      Arrow(t,t') -> bArrow (fn t) (fn t')
    | Forall (s,f) ->
        bForall s (fun x -> fn (subst f (TTVar x)))
    | Exists (s,f) ->
        bExists s (fun x -> fn (subst f (TTVar x)))
    | TTVar x -> x
    | Mu (s,f) ->
        bMu s (fun x -> fn (subst f (TTVar x)))
    | Nu (s,f) ->
        bNu s (fun x -> fn (subst f (TTVar x)))
    | TDef (t,tl) -> bTDef t (Array.map fn tl)
    | Pro l -> bPro (List.map (fun (s, t) -> (s, fn t)) l)
    | MCst _ -> raise (Subtype_fail "capture_one")
    | NCst _ -> raise (Subtype_fail "capture_one")
    | TUvr vc as t -> if vc == cv then x else unit t
    | TCst _|TStr _ -> unit t
  in fn c
;;

let capture_cst cv c x =
  let rec fn c =
    let t = normk c in
    match t with
      Arrow(t,t') -> bArrow (fn t) (fn t')
    | Forall (s,f) ->
        bForall s (fun x -> fn (subst f (TTVar x)))
    | Exists (s,f) ->
        bExists s (fun x -> fn (subst f (TTVar x)))
    | TTVar x -> x
    | Mu (s,f) ->
        bMu s (fun x -> fn (subst f (TTVar x)))
    | Nu (s,f) ->
       bNu s (fun x -> fn (subst f (TTVar x)))
    | Pro l ->
       bPro (List.map (fun (s,t) -> (s, fn t)) l)
    | TDef (t,tl) -> bTDef t (Array.map fn tl)
    | MCst _ -> raise (Subtype_fail "capture_one")
    | NCst _ -> raise (Subtype_fail "capture_one")
    | TCst vc as t -> if vc = cv then x else unit t
    | TUvr _|TStr _ -> unit t
  in fn c
;;

let rec subtype ctxt c c' =
  let t as c = normk c and t' as c' = normk c' in
  if !verbose then begin
    print_string "  "; print_ckind c;
    print_string " < "; print_ckind c';
    print_newline ()
  end;
  if t == t' then () else
  match t, t' with
    TUvr ({uvr_val = o} as vc), TUvr vc' ->
      if vc == vc' then () else
      if o <> Nothing then failwith "bug 1 in sub_type";
      if occur_prog vc c' <> None0 then assert false;
      vc.uvr_val <- Something c'
  | TUvr ({uvr_val = o} as vc), _ ->
      if o <> Nothing then failwith "bug 1 in sub_type";
      (match occur_prog vc c', !inductive with
        None0, _ ->
          vc.uvr_val <- Something c'
      | Pos, true ->
          vc.uvr_val <- Something (start_term (bNu "K"
                 (fun x -> capture_var vc c' x)))
      | _ ->
          vc.uvr_val <- Something (start_term (bForall "X"
                 (fun x -> capture_var vc c' x))))
  | _, TUvr ({uvr_val = o} as vc) ->
      if o <> Nothing then failwith "bug 1 in sub_type";
      (match occur_prog vc c, !inductive with
        None0, _ ->
          vc.uvr_val <- Something c
      | Pos, true ->
          vc.uvr_val <- Something (start_term (bMu "K"
                 (fun x -> capture_var vc c x)))
      | _ ->
          vc.uvr_val <- Something (start_term (bExists "X"
                 (fun x -> capture_var vc c x))))
  | TDef (t,tl),  TDef (t',tl') ->
      if t == t' && tl = [||] && tl' = [||] then ()
      else subtype ctxt (subst t.val_tdef tl) c'
  | TDef (t,tl), _ ->
      subtype ctxt (subst t.val_tdef tl) c'
  | _, TDef (t,tl) ->
      subtype ctxt c (subst t.val_tdef tl)
  | Mu(_,f), _ ->
      let v = TUvr (new_uvr ()) in
      let t = subst f v in
      subtype ctxt t c';
      subtype ctxt t v
  | Forall (_,f), _ ->
      let v = TUvr (new_uvr ()) in
      subtype ctxt (subst f v) c'
  | _, Nu(_,f') ->
      let v = TUvr (new_uvr ()) in
      let t' = subst f' v in
      subtype ctxt c t';
      subtype ctxt v t'
  | Nu(_,f), _ ->
      let n = new_cst () in
      add_cst n (t::ctxt);
      let ct = NCst (n, subst f) in
      let t = subst f ct in
      subtype ctxt t c'
  | _, Mu(_,f') ->
      let n = new_cst () in
      add_cst n (t'::ctxt);
      let ct = MCst (n, subst f') in
      let t = subst f' ct in
      subtype ctxt c t
  | _, Forall (_,f') ->
      let n = new_cst () in
      add_cst n (t'::ctxt);
      let ct = TCst (ref n) in
      subtype ctxt c (subst f' ct)
  | Exists (_,f), _ ->
      let n = new_cst () in
      add_cst n (t::ctxt);
      let ct = TCst (ref n) in
      subtype ctxt (subst f ct) c'
  | TCst n, TCst n' ->
      if !n <> !n' then
      if !n < 0 && !n' >= 0 then n := !n' else
      if !n >= 0 && !n' < 0 then n' := !n else
      raise (Subtype_fail "Clash")
  | MCst (n,_), (MCst (n',f') as ct) ->
      if n = n' then () else subtype ctxt c (f' ct)
  | (NCst (n,f) as ct), NCst (n',_) ->
      if n = n' then () else subtype ctxt (f ct) c'
  | _, (MCst (_,f') as ct) -> subtype ctxt c (f' ct)
  | (NCst (_,f) as ct), _ -> subtype ctxt (f ct) c'
  | _, Exists (_,f') ->
      let v = TUvr (new_uvr ()) in
      let ctxt = v::ctxt in
      subtype ctxt c (subst f' v)
  | Arrow(t,u), Arrow(t',u') ->
      let ctxt = t'::ctxt in
      subtype ctxt t' t;
      subtype ctxt u u'
  | (Pro l, Pro l') ->
     List.iter (fun (name,t') ->
       let t = try List.assoc name l with Not_found -> raise (Subtype_fail ("Clash: " ^ name)) in
       subtype ctxt t t') l'
  | _, _ -> raise (Subtype_fail "Clash")
;;

let equal t t' =
  subtype [] t t';
  subtype [] t' t
;;

let capture_cst_var cv cc cm cn c =
  let cs = List.fold_left (fun s (n,_) -> IntSet.add n s) IntSet.empty cc in
  let rec fn c =
    let t = normk c in
    match t with
      Arrow(t,t') -> bArrow (fn t) (fn t')
    | Forall (s,f) ->
        bForall s (fun x -> fn (subst f (TTVar x)))
    | Mu (s,f) ->
        bMu s (fun x -> fn (subst f (TTVar x)))
    | Exists (s,f) ->
        bExists s (fun x -> fn (subst f (TTVar x)))
    | Nu (s,f) ->
        bNu s (fun x -> fn (subst f (TTVar x)))
    | TDef (t,tl) -> bTDef t (Array.map fn tl)
    | TCst n as t -> (try List.assoc !n cc with Not_found -> unit t)
    | MCst (n,_) -> (try List.assoc n cm with Not_found -> unit t)
    | NCst (n,_) -> (try List.assoc n cn with Not_found -> unit t)
    | Pro l ->
       bPro (List.map (fun (s,t) -> (s, fn t)) l)
    | TUvr vc as t -> (
        try List.assq vc cv with Not_found ->
        if (not ((IntSet.is_empty (IntSet.inter cs vc.uvr_eig)))) then raise
          (Invalid_argument "capture") else unit t)
    | TTVar x -> x
    | _ -> unit t
  in fn c
;;

let do_capture cv cc cm cn c =
  if cv = [] && cc = [] && cm = [] && cn = [] then c else
  let rec fn cv = function
    v::l -> bForall "X" (fun x -> fn ((v,x)::cv) l)
  | [] ->
  let rec gn cc = function
    v::l -> bForall "X" (fun x -> gn ((v,x)::cc) l)
  | [] ->
  let rec hn cm = function
    v::l -> bMu "X" (fun x -> hn ((v,x)::cm) l)
  | [] ->
  let rec kn cn = function
    v::l -> bNu "X" (fun x -> kn ((v,x)::cn) l)
  | [] -> capture_cst_var cv cc cm cn c
  in kn [] cn
  in hn [] cm
  in gn [] cc
  in start_term (fn [] cv)
;;

module VarOrd = struct
  type t = var_cell
  let compare = fun v v' -> v.uvr_key - v'.uvr_key
end
module VarSet = Set.Make (VarOrd)

let var_set c = let rec fn s c =
  let t = normk c in
  match t with
    Arrow(t,t') -> fn (fn s t') t
  | Forall (_,f) | Mu (_,f) | Exists (_,f) | Nu (_,f) -> fn s (subst f dum_kind)
  | Pro l -> List.fold_left (fun s (_,t) -> fn s t) s l
  | TDef (t,tl) -> List.fold_left fn s (Array.to_list tl)
  | TUvr vc -> VarSet.add vc s
  | TCst _|MCst (_, _)|NCst (_, _)|TStr _|TTVar _ -> s
in
  fn VarSet.empty c
;;

let cst_set c = let rec fn s c =
  let t = normk c in
  match t with
    Arrow(t,t') -> fn (fn s t') t
  | Forall (_,f) | Mu (_,f) | Exists (_,f) | Nu (_,f) -> fn s (subst f dum_kind)
  | Pro l -> List.fold_left (fun s (_,t) -> fn s t) s l
  | TDef (t,tl) -> List.fold_left fn s (Array.to_list tl)
  | TCst vc -> IntSet.add !vc s
  | MCst (_, _)|NCst (_, _)|TUvr _|TStr _|TTVar _ -> s
in
  fn IntSet.empty c

let mcst_set c = let rec fn s c =
  let t = normk c in
  match t with
    Arrow(t,t') -> fn (fn s t') t
  | Forall (_,f) | Mu (_,f) | Exists (_,f) | Nu (_,f) -> fn s (subst f dum_kind)
  | Pro l -> List.fold_left (fun s (_,t) -> fn s t) s l
  | TDef (t,tl) -> List.fold_left fn s (Array.to_list tl)
  | MCst (n,_) -> IntSet.add n s
  | TCst _|NCst (_, _)|TUvr _|TStr _|TTVar _ -> s
in
  fn IntSet.empty c

let ncst_set c = let rec fn s c =
  let t = normk c in
  match t with
    Arrow(t,t') -> fn (fn s t') t
  | Forall (_,f) | Mu (_,f) | Exists (_,f) | Nu (_,f) -> fn s (subst f dum_kind)
  | Pro l -> List.fold_left (fun s (_,t) -> fn s t) s l
  | TDef (t,tl) -> List.fold_left fn s (Array.to_list tl)
  | NCst (n,_) -> IntSet.add n s
  | TCst _|MCst (_, _)|TUvr _|TStr _|TTVar _ -> s
in
  fn IntSet.empty c

let generalise ctxt c =
  let vars = VarSet.elements
    (List.fold_left (fun s c -> VarSet.diff s (var_set c)) (var_set c) ctxt) in
  let csts = IntSet.elements
    (List.fold_left (fun s c -> IntSet.diff s (cst_set c)) (cst_set c) ctxt) in
  let mcsts = IntSet.elements
    (List.fold_left (fun s c -> IntSet.diff s (mcst_set c)) (mcst_set c) ctxt) in
  let ncsts = IntSet.elements
    (List.fold_left (fun s c -> IntSet.diff s (ncst_set c)) (ncst_set c) ctxt) in
  do_capture vars csts mcsts ncsts c

let map_vect2 f v1 v2 =
  let l = Array.length v1 in
  if Array.length v2 <> l then raise (Invalid_argument "map_vect2");
  if l = 0 then [||] else begin
    let v = Array.create l (f v1.(0) v2.(0)) in
    for i = 1 to l - 1 do
      v.(i) <- f v1.(i) v2.(i)
    done; v
  end

let dum_info =
  {lbg = -1; cbg = -1; lnd = -1; cnd = -1}

let rec type_check ctxt t c =
  if !verbose then begin
    print_terme t;
    print_string " : ";
    print_ckind c;
    print_newline ()
  end;
  match t with
    Abs (i,i',s,k,f) ->
      let u = match k with
        Nothing -> TUvr (new_uvr ())
      | Something k -> k
      and u' = TUvr (new_uvr ()) in
      let c' = Arrow(u,u') in (
      try
        subtype ctxt c' c;
        type_check (u::ctxt) (subst f (TKVar (i',s,u))) u'
      with Subtype_fail _ | Sys.Break -> raise (Type_error (i,c',c)))

  | Cstr(i, name, t) ->
     let u = TUvr (new_uvr ()) in
     let c' = start_term (bSum [name, unit u]) in (
     try
       subtype ctxt c' c;
       type_check ctxt t u
     with Subtype_fail _ | Sys.Break -> raise (Type_error (i,c',c)))

  | Rec(i, l) ->
     let lu = List.map (fun (name, t) -> (name, TUvr (new_uvr ()))) l in
     let c' = Pro(lu) in (
     try
       subtype ctxt c' c;
       List.iter2 (fun (_,t) (_,u) -> type_check ctxt t u) l lu
     with Subtype_fail _ | Sys.Break -> raise (Type_error (i,c',c)))

  | App(_,t,Proj (_, name)) ->
     let c' = Pro([name, c]) in
     type_check ctxt t c'

  | App(_,t,t') ->
      let u = TUvr (new_uvr ()) in
      type_check ctxt t (Arrow(u,c));
      type_check ctxt t' u

  | IVar(i,TKVar (_,_,c')) -> (
      try subtype ctxt c' c
      with Subtype_fail _ | Sys.Break -> raise (Type_error (i,c',c)))

  | FVar (i,v) -> (
      match v.ttype with
        Nothing -> (
	  try type_check ctxt v.valeur c
	  with Type_error(i, c, c') ->
	    raise (Type_error(dum_info, c, c')))
      | Something c' ->
         try subtype ctxt c' c
         with Subtype_fail _ | Sys.Break ->
           raise (Type_error (i,c',c)))

  | Side (i,_) -> (
      try subtype ctxt idt c
      with Subtype_fail _ | Sys.Break -> raise (Type_error (i,idt,c)))

  | Let (i,b,sl,fv) ->
      let v = Array.map (fun (i,s) -> TUvr (new_uvr ())) sl in
      let nctxt = if (not (b)) then ctxt else (
        let ctxt = ref ctxt in
        for i = 1 to Array.length v - 1 do
          ctxt:=v.(i)::!ctxt
        done;
        !ctxt)
      in
      let v' = subst fv (map_vect2 (fun (i,s) k -> TKVar(i,s,k)) sl v) in
      for i = 1 to Array.length v' - 1 do
        type_check nctxt v'.(i) v.(i)
      done;
      let pctxt =
        let ctxt = ref ctxt in
        for i = 1 to Array.length v - 1 do
          v.(i) <- generalise nctxt v.(i);
          ctxt:=v.(i)::!ctxt
        done;
        !ctxt
      in
      let v' = subst fv (map_vect2 (fun (i,s) k -> TKVar(i,s,k)) sl v) in
      type_check pctxt v'.(0) c

  | Ass (i,t,c') -> (
      try
        subtype ctxt c' c;
        type_check ctxt t c'
      with Subtype_fail _ | Sys.Break -> raise (Type_error (i,c',c)))

  | Lam (i, _, t) ->
      let n = new_cst () in
      let v = TCst (ref (-n)) in
      add_cst (-n) ctxt;
      type_check ctxt (subst t v) c

  | _ -> failwith "bug in type_check"
;;

let type_inf t =
  let u = TUvr (new_uvr ()) in
  type_check [] t u;
  generalise [] u
;;

let type_chck t = function
  Nothing -> type_inf t
| Something k -> type_check [] t k; generalise [] k
;;

(*
(**) #open "profile";;
let type_inf = profile "type_inf" type_inf;;
let type_chck = profile2 "type_chck" type_chck;;
*)
