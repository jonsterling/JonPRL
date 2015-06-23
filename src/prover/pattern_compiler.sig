signature PATTERN_COMPILER =
sig
  type label
  type term
  type pattern
  type conv = term -> term

  type rule = {definiendum : pattern, definiens : term}
  val compile : rule -> conv
end
