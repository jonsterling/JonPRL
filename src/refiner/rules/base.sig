signature BASE_RULES =
sig
  type tactic
  type hyp
  type name

  val Eq : tactic
  val Intro : tactic
  val MemberEq : tactic
  val AtomSubtypeBase : tactic
  val ElimEq : hyp * name option -> tactic
end
