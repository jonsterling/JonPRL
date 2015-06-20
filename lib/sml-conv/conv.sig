signature CONV =
sig
  type term
  type conv = term -> term
  exception Conv
end

signature CONV_UTIL =
sig
  include CONV
  structure Syntax : ABT where type t = term

  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t
  val reductionRule : red -> conv
end
