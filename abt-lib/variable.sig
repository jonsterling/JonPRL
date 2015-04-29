signature VARIABLE =
sig
  type t
  type ord_key

  val new : unit -> t
  val named : string -> t

  val eq : t -> t -> bool
  val compare : t * t -> order

  val to_string : t -> string
end

