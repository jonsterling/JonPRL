signature CONV_TYPES =
sig
  structure Syntax : ABT_UTIL

  type conv = Syntax.t -> Syntax.t
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  val reductionRule : red -> conv

  exception Conv
end

signature CONV_COMPILER =
sig
  include CONV_TYPES

  type rule = {definiendum : Syntax.t, definiens : Syntax.t}
  val compile : rule -> conv
end
