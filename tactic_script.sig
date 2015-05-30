signature TACTIC_SCRIPT =
sig
  structure Lcf : LCF
  val parse : Lcf.tactic CharParser.charParser
end
