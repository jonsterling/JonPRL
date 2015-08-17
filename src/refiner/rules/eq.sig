signature EQ_RULES =
sig
  type tactic

  val EqEq : tactic
  val EqEqBase : tactic
  val EqMemEq : tactic
end
