signature DEVELOPMENT_PARSER =
sig
  structure Development : DEVELOPMENT
  exception RemainingSubgoals of Development.judgement list
  val parse : Development.world -> Development.world CharParser.charParser
end
