signature PARSE_ABT =
sig
  include ABT_UTIL

  structure ParseOperator : PARSE_OPERATOR
  sharing Operator = ParseOperator

  type env
  val parse_abt : env -> t CharParser.charParser
end

