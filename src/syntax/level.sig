signature LEVEL =
sig
  eqtype t
  val toString : t -> string

  exception LevelError
  val assertLt : t * t -> unit
  val unify : t * t -> t
  val max : t * t -> t

  val succ : t -> t
  val pred : t -> t
  val base : t

  val parse : t CharParser.charParser
end

