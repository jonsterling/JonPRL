signature EQ_RULES =
sig
  type tactic
  type term

  val EqEq : tactic
  val EqEqBase : tactic
  val EqMemEq : tactic
  val EqSubst : term * term * Level.t option -> tactic
  val EqSym : tactic
end
