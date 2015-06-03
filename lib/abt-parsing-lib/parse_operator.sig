signature PARSE_OPERATOR =
sig
  include OPERATOR

  val parse_operator : t CharParser.charParser
end
