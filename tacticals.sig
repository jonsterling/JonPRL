signature TACTICALS =
sig
  type tactic

  val ID : tactic
  val THEN : tactic * tactic -> tactic
  val THENL : tactic * tactic list -> tactic
  val THEN_LAZY : tactic * (unit -> tactic) -> tactic
  val THENL_LAZY : tactic * (unit -> tactic list) -> tactic
  val REPEAT : tactic -> tactic

  val ORELSE : tactic * tactic -> tactic
  val ORELSE_LAZY : tactic * (unit -> tactic) -> tactic
  val TRY : tactic -> tactic
end

