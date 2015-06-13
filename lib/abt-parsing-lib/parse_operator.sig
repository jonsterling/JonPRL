signature PARSE_OPERATOR =
sig
  include OPERATOR

  type env
  val parseOperator : env -> t CharParser.charParser
end
