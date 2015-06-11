signature TACTIC_SCRIPT =
sig
  structure Lcf : LCF

  type env
  val parse : env -> Lcf.tactic CharParser.charParser
end
