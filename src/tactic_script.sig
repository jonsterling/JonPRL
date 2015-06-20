signature TACTIC_SCRIPT =
sig
  type tactic
  type env
  val parse : env -> tactic CharParser.charParser
end
