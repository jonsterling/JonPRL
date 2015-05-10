signature CONTEXT =
sig

  type name
  type 'a context

  val empty : 'a context

  val insert : 'a context -> name -> 'a -> 'a context
  val remove : 'a context -> name -> 'a context * 'a

  val lookup : 'a context -> name -> 'a option
  val search : 'a context -> ('a -> bool) -> (name * 'a) option

  val map : ('a -> 'b) -> 'a context -> 'b context
  val mapi : (name * 'a -> 'b) -> 'a context -> 'b context

  val eq : ('a * 'a -> bool) -> 'a context * 'a context -> bool

  val foldri : ((name * 'a * 'b) -> 'b) -> 'b -> 'a context -> 'b

  val to_string : PrintMode.t * (PrintMode.t -> 'a -> string) -> 'a context -> string

end
