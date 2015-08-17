signature ISECT_RULES =
sig
  type tactic
  type name
  type term
  type hyp

  val IsectEq : name option -> tactic
  val IsectIntro : name option * Level.t option -> tactic
  val IsectElim : hyp * term * (name * name) option -> tactic
  val IsectMemberEq : name option * Level.t option -> tactic
  val IsectMemberCaseEq : term option * term -> tactic
end
