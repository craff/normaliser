(* functions and type to use binder *)

(* this exception is raised when you call start_term on a term with free*)
(* variable *)
exception Bindlib_error

(* this is the type of an expression of type 'b with a bound variable of *)
(* type 'a *)
type ('a,'b) binder

(* this is the subtitution function: it takes an expression with a bound*)
(* variable of type 'a and a value for this variable and replace all the*)
(* occurrence of this variable by this value *)
val subst : ('a,'b) binder -> 'a -> 'b

(* the type of an object of type 'a being constructed (this object may have*)
(* free variable *)
type 'a pre_term

(* the function to call when the construction of an expression of type 'a is*)
(* finished. The expression must have no free variable !*)
val start_term : 'a pre_term -> 'a

(* unit allows you to use an expression of type 'a in a larger expression*)
(* begin constructed with free variables *) 
val unit : 'a -> 'a pre_term

(* this is THE function constructing binder. If takes an expression of type*)
(* 'a pre_term -> 'b pre_term in general written (fun x -> expr) (we say that*)
(* x is a free variable of expr). And it construct the binder that build the*)
(* expression where x is bound *)
val bind :
 ('a pre_term -> 'b pre_term) -> ('a,'b) binder pre_term

(* this is THE function that allows you to construct expression by allowing*)
(* the application of a function with free variable to an argument with free*)
(* variable *)
val apply : 
 ('a -> 'b) pre_term -> 'a pre_term -> 'b pre_term

(* The following function can be written using unit and apply but are given*)
(* because they are very usefull. Moreover, some of them are optimised *)
val unit_apply : 
 ('a -> 'b) -> 'a pre_term -> 'b pre_term

val unit_apply2 : 
 ('a -> 'b -> 'c) -> 'a pre_term -> 'b pre_term -> 'c pre_term

val unit_apply3 : 
 ('a -> 'b -> 'c -> 'd) -> 'a pre_term -> 
   'b pre_term  -> 'c pre_term -> 'd pre_term

val build_pair :
 'a pre_term -> 'b pre_term -> ('a * 'b) pre_term

val build_list :
 'a pre_term list -> 'a list pre_term

val build_array :
 'a pre_term array -> 'a array pre_term

