signature TACTIC_SCRIPT =
sig
  structure Lcf : LCF

  type state
  val parse : (state -> Lcf.tactic) CharParser.charParser
end
