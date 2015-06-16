signature CONV_COMPILER =
sig
  include CONV_TYPES

  type label
  structure PatternSyntax : ABT_UTIL
    where type Operator.t = label PatternOperatorType.operator

  type rule = {definiendum : PatternSyntax.t, definiens : Syntax.t }
  val compile : rule -> conv
end
