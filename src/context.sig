signature CONTEXT =
sig
  structure Syntax : ABT_UTIL
  type name = Syntax.Variable.t
  type term = Syntax.t
  type context

  val fresh : context * name -> name

  val empty : context
  val is_empty : context -> bool

  val insert : context -> name -> Visibility.t -> term -> context
  val interpose_after : context -> name * context -> context

  val modify : context -> name -> (term -> term) -> context

  exception NotFound of name
  val lookup : context -> name -> term
  val lookup_visibility : context -> name -> term * Visibility.t

  val nth : context -> int -> name

  val search : context -> (term -> bool) -> (name * term) option

  val map : (term -> term) -> context -> context
  val map_after : name -> (term -> term) -> context -> context
  val list_items : context -> (name * Visibility.t * term) list

  val to_string : context -> string

  val eq : context * context -> bool
  val subcontext : context * context -> bool

  val rebind : context -> term -> term
end
