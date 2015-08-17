signature IMAGE_RULES =
sig
  type tactic
  type hyp
  type name

  val ImageEq    : tactic
  val ImageMemEq : tactic
  val ImageElim  : hyp * name option -> tactic
  val ImageEqInd : hyp * (name * name * name * name) option -> tactic
end
