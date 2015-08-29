signature NEIGHBORHOOD_RULES =
sig
  type tactic
  type term
  type hyp
  type name

  val Eq : tactic
  val MemEq : Level.t option -> tactic

  val Elim : hyp * (name * name * name) option -> tactic
  val IndEq : term option * term option * (name * name * name) option -> tactic
end
