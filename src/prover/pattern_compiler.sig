signature PATTERN_COMPILER =
sig
  type label
  type term
  type conv = term -> term

  type rule = {definiendum : term, definiens : term}
  val compile : rule -> conv
end
