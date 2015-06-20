signature TACTIC_SCRIPT =
sig
  type tactic
  type world
  val parse : world -> tactic CharParser.charParser
end
