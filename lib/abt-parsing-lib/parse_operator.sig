signature PARSE_OPERATOR =
sig
  include OPERATOR

  type world
  val parseOperator : world -> t CharParser.charParser
end
