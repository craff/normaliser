open Lambda;;

exception Subtype_fail of string;;
exception Type_error of info * kind * kind;;

val subtype : kind list -> kind -> kind -> unit;;
val equal : kind -> kind -> unit;;
val type_chck : terme -> kind obj -> kind;;
val type_inf : terme -> kind;;
