signature FUN_RULES =
sig
  type tactic
  type term
  type name
  type hyp

  val Eq : name option -> tactic
  val Intro : name option * Level.t option -> tactic
  val Elim : hyp * term * (name * name) option -> tactic
  val LamEq : name option * Level.t option -> tactic
  val ApEq : term option -> tactic
  val FunExt : name option * Level.t option -> tactic
end
