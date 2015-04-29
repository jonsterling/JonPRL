signature OPERATOR =
sig
  type t

  val eq : t -> t -> bool
  val arity : t -> int vector
  val to_string : t -> string

end
