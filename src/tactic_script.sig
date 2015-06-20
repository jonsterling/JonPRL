signature TACTIC_SCRIPT =
sig
  structure Tacticals : TACTICALS

  type tactic = Tacticals.tactic
  type world

  val parse : world -> tactic CharParser.charParser
  val parseComplete : world -> tactic CharParser.charParser
end
