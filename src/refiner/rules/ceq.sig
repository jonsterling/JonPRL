signature CEQ_RULES =
sig
  type tactic
  type term
  type hyp

  val Eq       : tactic
  val MemEq    : tactic
  val Sym      : tactic
  val Step     : tactic
  val Subst    : term * term -> tactic
  val HypSubst : Dir.dir * hyp * term -> tactic
  val Struct   : tactic
  val Approx   : tactic
end
