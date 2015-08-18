signature CEQ_RULES =
sig
  type tactic
  type term
  type hyp

  val CEqEq       : tactic
  val CEqMemEq    : tactic
  val CEqSym      : tactic
  val CEqStep     : tactic
  val CEqSubst    : term * term -> tactic
  val HypCEqSubst : Dir.dir * hyp * term -> tactic
  val CEqStruct   : tactic
  val CEqApprox   : tactic
end
