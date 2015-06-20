signature PARSE_ABT =
sig
  include ABT_UTIL

  structure ParseOperator : PARSE_OPERATOR
  sharing type Operator.t = ParseOperator.t

  val parseAbt : Variable.t list -> ParseOperator.env -> t CharParser.charParser
end

