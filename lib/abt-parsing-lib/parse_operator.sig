signature PARSE_OPERATOR =
sig
  include OPERATOR

  type env
  val parse_operator : env -> t CharParser.charParser
end
