signature ATOM_RULES =
sig
  type tactic
  type name

  val AtomEq : tactic
  val TokenEq : tactic
  val TestAtomEq : name option -> tactic
  val TestAtomReduceLeft : tactic
  val TestAtomReduceRight : tactic
  val MatchTokenEq : tactic
end
