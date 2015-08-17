signature SUBSET_RULES =
sig
  type name
  type tactic
  type term
  type hyp

  val SubsetEq : name option -> tactic
  val SubsetIntro : term * name option * Level.t option -> tactic
  val IndependentSubsetIntro : tactic
  val SubsetElim : hyp * (name * name) option -> tactic
  val SubsetMemberEq : name option * Level.t option -> tactic
  val EqInSupertype : tactic
end
