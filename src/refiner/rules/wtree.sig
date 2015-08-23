signature WTREE_RULES =
sig
  type tactic
  type name
  type term
  type hyp

  val Eq : tactic
  val MemEq : tactic
  val RecEq : term option * term -> tactic

  val Intro : term * name option -> tactic
  val Elim : hyp * (name * name * name) option -> tactic
end
