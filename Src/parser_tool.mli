open Lambda;;
open Bindlib;;

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

val merge_info : info -> info -> info;;
val merge_info_ass : info -> (info * 'a) obj -> info * 'a obj;;

val pkind2kind : (string * pCell) list -> pkind -> kind pre_term;;
val pterme2terme : (string * (unit -> terme pre_term)) list
  -> (string * pCell) list -> pterme -> terme pre_term;;

val finalise : pterme -> terme;;
val cur_input : in_channel ref;;
val cur_name : string ref;;
val cur_line : int ref;;
val cur_col : int ref;;
val pv_col : int ref;;
val pv_lin : int ref;;

val pop_input : unit -> unit;;
val pop_all : unit -> unit;;

val path : string list ref;;
val init : bool ref;;
val read_file : string -> unit;;
val read_fun : bytes -> int -> int;;
val test_console : unit -> bool;;
val print_input : info -> unit;;
val is_end_of_file : unit -> bool;;
val start_new : bool ref;;
