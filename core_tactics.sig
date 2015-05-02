signature CORE_TACTICS =
sig
  type tactic
  val ID : tactic
  val THEN : tactic * tactic -> tactic
  val THEN_LAZY : tactic * (unit -> tactic) -> tactic
  val REPEAT : tactic -> tactic

  val ORELSE : tactic * tactic -> tactic
  val ORELSE_LAZY : tactic * (unit -> tactic) -> tactic
end

