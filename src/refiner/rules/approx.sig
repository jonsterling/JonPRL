signature APPROX_RULES =
sig
  type tactic
  type hyp
  type name
  type term

  val ApproxEq    : tactic
  val ApproxMemEq : tactic
  val ApproxExtEq : tactic
  val ApproxElim : hyp -> tactic
  val ApproxRefl  : tactic
  val BottomDiverges : hyp -> tactic
  val AssumeHasValue : (name option * Level.t option) -> tactic
end
