signature UNIV_RULES =
sig
  type tactic

  val Cum : Level.t option -> tactic
  val UnivEq : tactic
end
