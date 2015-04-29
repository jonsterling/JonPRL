signature VECTORUTIL =
sig

  val zip : 'a vector -> 'b vector -> ('a * 'b) vector

  val pair_all   : ('a * 'b -> bool) -> 'a vector -> 'b vector -> bool
  val pair_all_eq : ('a * 'b -> bool) -> 'a vector -> 'b vector -> bool

  val to_string : ('a -> string) -> 'a vector -> string

end
