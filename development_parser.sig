signature DEVELOPMENT_PARSER =
sig
  structure Development : DEVELOPMENT
  val parse : Development.t -> Development.t CharParser.charParser
end
