signature ISECT_RULES =
sig
  type tactic
  type name
  type term
  type hyp

  val Eq : name option -> tactic
  val Intro : name option * Level.t option -> tactic
  val Elim : hyp * term * (name * name) option -> tactic
  val MemberEq : name option * Level.t option -> tactic
  val MemberCaseEq : term option * term -> tactic
end
