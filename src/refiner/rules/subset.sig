signature SUBSET_RULES =
sig
  type name
  type tactic
  type term
  type hyp

  val Eq : name option -> tactic
  val Intro : term * name option * Level.t option -> tactic
  val IndependentIntro : tactic
  val Elim : hyp * (name * name) option -> tactic
  val MemberEq : name option * Level.t option -> tactic
  val EqInSupertype : tactic
end
