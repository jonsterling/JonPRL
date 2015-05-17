signature CONTEXT =
sig
  structure Name : VARIABLE

  type name = Name.t
  type 'a context

  val fresh : 'a context * name -> name

  val empty : 'a context

  val insert : 'a context -> name -> 'a -> 'a context
  val remove : 'a context -> name -> 'a context * 'a

  exception NotFound of name
  val lookup : 'a context -> name -> 'a

  val search : 'a context -> ('a -> bool) -> (name * 'a) option

  val map : ('a -> 'b) -> 'a context -> 'b context
  val foldri : ((name * 'a * 'b) -> 'b) -> 'b -> 'a context -> 'b

  val to_string : PrintMode.t * (PrintMode.t -> 'a -> string) -> 'a context -> string

  val eq : ('a * 'a -> bool) -> 'a context * 'a context -> bool
  val subcontext : ('a * 'a -> bool) -> 'a context * 'a context -> bool
end
