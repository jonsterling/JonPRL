signature CONTAINER_EXTENSION_RULES =
sig
  type tactic
  type hyp
  type name

  val Eq : tactic
  val MemEq : tactic
  val Elim : hyp * (name * name) option -> tactic
end
