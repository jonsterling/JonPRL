signature CONV_COMPILER =
sig
  include CONV_TYPES

  structure Label : LABEL

  structure PatternSyntax : ABT_UTIL
    where type Operator.t = Label.t PatternOperatorType.operator

  type rule = {definiendum : PatternSyntax.t, definiens : Syntax.t }
  val compile : rule -> conv
end
