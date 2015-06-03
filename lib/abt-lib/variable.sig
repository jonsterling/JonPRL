signature VARIABLE =
sig
  type t
  val named : string -> t

  val eq : t * t -> bool
  val compare : t * t -> order

  val name : t -> string
  val to_string : t -> string

  val clone : t -> t
  val prime : t -> t
end

