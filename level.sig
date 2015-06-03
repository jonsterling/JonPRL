signature LEVEL =
sig
  eqtype t

  exception LevelError

  val base : t
  val prime : t -> t
  val pred : t -> t
  val max : t * t -> t

  type constraint
  type substitution

  val yank : t -> substitution
  val unify : t * t -> constraint
  val resolve : constraint list -> substitution
  val subst : substitution -> t -> t

  val compare : t * t -> order
  val assert_lt : t * t -> unit
  val assert_lte : t * t -> unit
  val assert_eq : t * t -> t

  val to_string : t -> string
  val parse : t CharParser.charParser
end
