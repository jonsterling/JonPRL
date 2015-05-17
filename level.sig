signature LEVEL =
sig
  type t
  val to_string : t -> string

  exception LevelError
  val assert_lt : t * t -> unit
  val unify : t * t -> t
  val max : t * t -> t
end

