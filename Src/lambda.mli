open Bindlib;;

val print_newline : unit -> unit;;
val print_endline : string -> unit;;
val params : (string * ((int -> unit) * (unit -> int))) list;;

type info = {lbg:int; cbg:int; lnd:int; cnd:int};;

type  'a obj =
  Nothing
| Something of 'a
;;

type occur = None0 | Pos | Neg | Both;;

module IntOrd : Set.OrderedType
module IntSet : Set.S with type elt = int
module StringOrd : Set.OrderedType
module StringSet : Set.S with type elt = string

val not_occur : occur -> occur;;
val and_occur : occur -> occur -> occur;;

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
  | Cstr of info * string * terme
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

val bproj : int -> 'a array pre_term -> 'a pre_term;;
val bMu : string -> (kind pre_term -> kind pre_term) -> kind pre_term;;
val bForall : string -> (kind pre_term -> kind pre_term) -> kind pre_term;;
val bNu : string -> (kind pre_term -> kind pre_term) -> kind pre_term;;
val bExists : string -> (kind pre_term -> kind pre_term) -> kind pre_term;;
val bArrow : kind pre_term -> kind pre_term -> kind pre_term;;
val bSum : (string * kind pre_term) list -> kind pre_term;;
val bPro : (string * kind pre_term) list -> kind pre_term;;
val bTDef : tdef -> kind pre_term array -> kind pre_term;;
val bTCst : int -> kind pre_term;;
val bTUvr : var_cell -> kind pre_term;;
val bApp : info -> terme pre_term -> terme pre_term -> terme pre_term;;
val bAbs : info -> info -> string -> kind obj pre_term -> (terme pre_term -> terme pre_term) -> terme pre_term;;
val bLet : info -> bool -> (info * string) array ->
  (terme array pre_term -> terme pre_term array) -> terme pre_term;;
val bSide : info -> string -> terme pre_term;;
val bFVar : info -> valeur -> terme pre_term;;
val bLam : info -> string -> (kind pre_term -> terme pre_term) -> terme pre_term;;
val bAss : info -> terme pre_term -> kind pre_term -> terme pre_term;;
val bIVar : info -> terme pre_term -> terme pre_term;;
val bProj : info -> string -> terme pre_term;;
val bCstr : info -> string -> terme pre_term -> terme pre_term;;
val bCase : info -> (string * terme pre_term) list -> terme pre_term;;
val bRec : info -> (string * terme pre_term) list -> terme pre_term;;
val reset_cst : unit -> unit;;
val new_cst : unit -> int;;
val reset_uvr : unit -> unit;;
val new_uvr : unit -> var_cell;;

val idt : kind;;
val dum_kind : kind;;
val dum_terme : terme;;
val dum_cterme : cterme;;

val build_sign : int -> (kind array,kind) binder -> occur array;;

val mode : mode ref;;
val recursive : bool ref;;
val typed : bool ref;;
val verbose : bool ref;;
val inductive : bool ref;;
val print_toggle : bool ref -> unit;;

val terme2cterme : terme -> cterme;;
val env : env_table;;
val tenv : tenv_table;;
val add_used : string -> unit;;
val print_terme : terme -> unit;;
val print_ckind : kind -> unit;;
val prrec_terme : terme -> unit;;

val norm : cterme -> unit;;
