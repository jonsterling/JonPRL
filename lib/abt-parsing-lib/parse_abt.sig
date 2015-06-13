signature PARSE_ABT =
sig
  include ABT_UTIL

  structure ParseOperator : PARSE_OPERATOR
  sharing Operator = ParseOperator

  val parse_abt : Variable.t list -> ParseOperator.env -> t CharParser.charParser
end

