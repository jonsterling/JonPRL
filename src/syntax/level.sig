signature LEVEL =
sig
  eqtype t
  val toString : t -> string

  val base : t
  val succ : t -> t
  val pred : t -> t
  val max : t * t -> t

  type constraint
  type substitution

  val yank : t -> substitution
  val unify : t * t -> constraint
  val resolve : constraint list -> substitution
  val subst : substitution -> t -> t

  exception LevelError
  val assertLt : t * t -> unit
  val assertEq : t * t -> unit

  val parse : t CharParser.charParser
end

