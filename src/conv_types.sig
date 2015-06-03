signature CONV_TYPES =
sig
  structure Syntax : ABT_UTIL

  type conv = Syntax.t -> Syntax.t
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  val reduction_rule : red -> conv

  exception Conv
end
