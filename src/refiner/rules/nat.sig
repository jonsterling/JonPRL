signature NAT_RULES =
sig
  type tactic
  type name
  type hyp
  type term

  val NatEq : tactic
  val NatElim : hyp * (name * name) option -> tactic
  val ZeroEq : tactic
  val SuccEq : tactic
  val NatRecEq : term option * (name * name) option -> tactic
end
