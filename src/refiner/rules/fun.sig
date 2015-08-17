signature FUN_RULES =
sig
  type tactic
  type term
  type name
  type hyp

  val FunEq : name option -> tactic
  val FunIntro : name option * Level.t option -> tactic
  val FunElim : hyp * term * (name * name) option -> tactic
  val LamEq : name option * Level.t option -> tactic
  val ApEq : term option -> tactic
  val FunExt : name option * Level.t option -> tactic
end
