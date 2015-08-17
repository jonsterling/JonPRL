signature EQ_RULES =
sig
  structure Lcf : LCF

  val EqEq : Lcf.tactic
  val EqEqBase : Lcf.tactic
  val EqMemEq : Lcf.tactic
end
