signature LEVEL =
sig
  type t
  val toString : t -> string

  exception LevelError
  val assertLt : t * t -> unit
  val unify : t * t -> t
  val max : t * t -> t
end

