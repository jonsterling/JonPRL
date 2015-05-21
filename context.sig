signature CONTEXT =
sig
  structure Name : VARIABLE

  type name = Name.t
  type 'a context

  val fresh : 'a context * name -> name

  val empty : 'a context

  val insert : 'a context -> name -> Visibility.t -> 'a -> 'a context
  val remove : 'a context -> name -> 'a context * 'a

  val modify : 'a context -> name -> ('a -> 'a) -> 'a context

  exception NotFound of name
  val lookup : 'a context -> name -> 'a
  val lookup_visibility : 'a context -> name -> 'a * Visibility.t
  val search : 'a context -> ('a -> bool) -> (name * 'a) option

  val map : ('a -> 'b) -> 'a context -> 'b context
  val map_after : name -> ('a -> 'a) -> 'a context -> 'a context
  val list_items : 'a context -> (name * Visibility.t * 'a) list

  val to_string : PrintMode.t * (PrintMode.t -> 'a -> string) -> 'a context -> string

  val eq : ('a * 'a -> bool) -> 'a context * 'a context -> bool
  val subcontext : ('a * 'a -> bool) -> 'a context * 'a context -> bool
end
