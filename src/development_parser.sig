signature DEVELOPMENT_PARSER =
sig
  structure Development : DEVELOPMENT
  val parse : Development.world -> Development.world CharParser.charParser
end
