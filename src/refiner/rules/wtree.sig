signature WTREE_RULES =
sig
  type tactic
  type name
  type term
  type hyp

  val Eq : tactic
  val MemEq : tactic
end