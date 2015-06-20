functor Conv (Syntax : ABT_UTIL) : CONV =
struct
  type term = Syntax.t
  type conv = term -> term

  exception Conv
end

functor ConvUtil (structure Conv : CONV and Syntax : ABT where type t = Conv.term) : CONV_UTIL =
struct
  open Conv
  open Syntax
  structure Syntax = Syntax

  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t
  fun reductionRule red = red o map out o out
end
