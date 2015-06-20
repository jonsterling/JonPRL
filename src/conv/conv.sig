signature CONV =
sig
  structure Syntax : ABT_UTIL
  type conv = Syntax.t -> Syntax.t
  exception Conv
end

signature CONV_UTIL =
sig
  include CONV
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t
  val reductionRule : red -> conv
end
