signature CEQ_RULES =
sig
  type tactic
  type term
  type hyp
  type name

  val Eq       : tactic
  val MemEq    : tactic
  val Sym      : tactic
  val Step     : tactic
  val Subst    : term * term option -> tactic
  val HypSubst : Dir.dir * hyp * term option -> tactic
  val Struct   : tactic
  val Approx   : tactic
  val Elim     : hyp * (name * name) option -> tactic
end
