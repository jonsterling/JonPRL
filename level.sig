signature LEVEL =
sig
  type t
  val to_string : t -> string

  exception LevelError
  val compare : t * t -> order
  val assert_lt : t * t -> unit
  val unify : t * t -> t
  val max : t * t -> t
  val prime : t -> t
end
