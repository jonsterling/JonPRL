signature LEVEL_SOLVER =
sig
  structure Level : LEVEL
  type term

  exception LevelSolver

  val generateConstraints : term * term -> Level.constraint list
  val subst : Level.substitution -> term -> term
end

signature SYNTAX_WITH_UNIVERSES =
sig
  include ABT
  structure Level : LEVEL

  val mapLevel : Level.substitution -> Operator.t -> Operator.t
  val getLevelParameter : Operator.t -> Level.t option
  val eqModLevel : Operator.t * Operator.t -> bool
end
