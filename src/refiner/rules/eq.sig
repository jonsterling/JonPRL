signature EQ_RULES =
sig
  type tactic
  type term
  type hyp

  val EqEq : tactic
  val EqEqBase : tactic
  val EqMemEq : tactic
  val EqSym : tactic
  val EqSubst : term * term * Level.t option -> tactic
  val HypEqSubst : Dir.dir * hyp * term * Level.t option -> tactic
end
