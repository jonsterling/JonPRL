signature CORE_TACTICS =
sig
  type tactic
  val THEN : tactic * tactic -> tactic
  val ORELSE : tactic * tactic -> tactic
end
