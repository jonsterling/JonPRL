functor Conv (Syntax : ABT_UTIL) : CONV =
struct
  structure Syntax = Syntax
  type conv = Syntax.t -> Syntax.t

  exception Conv
end

functor ConvUtil (Conv : CONV) : CONV_UTIL =
struct
  open Conv
  open Syntax

  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t
  fun reductionRule red = red o map out o out
end
