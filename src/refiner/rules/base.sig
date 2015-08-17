signature BASE_RULES =
sig
  type tactic
  type hyp
  type name

  val BaseEq : tactic
  val BaseIntro : tactic
  val BaseMemberEq : tactic
  val BaseElimEq : hyp * name option -> tactic
end
