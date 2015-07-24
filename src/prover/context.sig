signature CONTEXT =
sig
  structure Syntax : ABT_UTIL
  structure Telescope : TELESCOPE
    where type Label.t = Syntax.Variable.t

  type name = Syntax.Variable.t
  type term = Syntax.t
  type context = (term * Visibility.t) Telescope.telescope

  val fresh : context * name -> name

  val empty : context
  val isEmpty : context -> bool

  val insert : context -> name -> Visibility.t -> term -> context
  val interposeAfter : context -> name * context -> context

  val modify : context -> name -> (term -> term) -> context

  exception NotFound of name
  val lookup : context -> name -> term
  val lookupVisibility : context -> name -> term * Visibility.t

  val nth : context -> int -> name

  val search : context -> (term -> bool) -> (name * term) option

  val map : (term -> term) -> context -> context
  val mapAfter : name -> (term -> term) -> context -> context
  val listItems : context -> (name * Visibility.t * term) list

  val toString : context -> string

  val eq : context * context -> bool
  val subcontext : context * context -> bool

  exception Open of term
  val rebindName : context -> name -> name
  val rebind : context -> term -> term
end
