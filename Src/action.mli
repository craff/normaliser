open Lambda;;
open Parser_tool;;

val action_let :  info -> bool -> bool -> 
  (info * string * pterme * pkind obj) list -> unit;;
val action_type : string -> (info * string) list -> pkind -> unit;;
val action_toggle : bool ref -> bool -> unit;;
val action_include : string -> unit;;
val action_path : string -> unit;;
val action_print_path : unit -> unit;;
val action_mode : mode -> unit;;
val action_print_mode : unit -> unit;;
val action_print : pterme -> unit;;
val action_prrec : pterme -> unit;;
(*value action_trace_all : bool -> unit;;*)
val action_trace_one : info * string -> int * bool -> unit;;
val action_print_trace : unit -> unit;;
val action_norm : pterme -> unit;;
val action_untyped : info -> pterme -> unit;;
val action_print_param : string -> unit;;
val action_param : string -> int -> unit;;

exception Wrong_untyped of info
