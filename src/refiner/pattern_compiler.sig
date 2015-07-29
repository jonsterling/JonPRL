signature PATTERN_TERM =
sig
  include ABT

  val asInstantiate : t -> (t * t) option
  val patternForOperator : Operator.t -> t
end

signature PATTERN_COMPILER =
sig
  structure PatternTerm : PATTERN_TERM

  type term = PatternTerm.t
  type conv = term -> term

  type rule = {definiendum : term, definiens : term}
  val compile : rule -> conv
end
