signature PROD_RULES =
sig
  type name
  type tactic
  type term
  type hyp

  val ProdEq : name option -> tactic
  val ProdIntro : term * name option * Level.t option -> tactic
  val IndependentProdIntro : tactic
  val ProdElim : hyp * (name * name) option -> tactic
  val PairEq : name option * Level.t option -> tactic
  val SpreadEq : term option * term option * (name * name * name) option -> tactic
end
