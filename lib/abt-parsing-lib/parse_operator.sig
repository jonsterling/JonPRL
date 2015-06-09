signature PARSE_OPERATOR =
sig
  include OPERATOR

  type state
  val parse_operator : (state -> t) CharParser.charParser
end
