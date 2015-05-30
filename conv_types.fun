functor ConvTypes (Syn : ABT_UTIL) : CONV_TYPES =
struct
  structure Syntax = Syn
  type conv = Syn.t -> Syn.t
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  open Syntax

  fun reduction_rule red M = red (map out (out M))
  exception Conv
end

structure ConvTypes = ConvTypes (Syntax)
