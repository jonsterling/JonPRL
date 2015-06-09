signature CONV_TYPES =
sig
  structure Syntax : ABT_UTIL

  type conv = Syntax.t -> Syntax.t
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  val reduction_rule : red -> conv

  exception Conv
end

signature CONV_COMPILER =
sig
  include CONV_TYPES

  type rule = {input : Syntax.t, output : Syntax.t}
  val compile : rule -> conv
end
