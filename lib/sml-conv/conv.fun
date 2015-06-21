(* In order to construct a module ascribing CONV from an ABT_UTIL
 * ascribing structure one may use Conv. This uses Syntax.t
 * for terms.
 *)
functor Conv (Syntax : ABT_UTIL) : CONV =
struct
  type term = Syntax.t
  type conv = term -> term

  exception Conv
end

(* ConvUtil provides a simple way to construct CONV_UTIL if you have
 * a structure ascribing ABT and a CONV ascribing structure which
 * have the same type. This is the sort of thing you might get
 * from Conv above.
 *
 * The default implementation of [reductionRule] simply unfolds a term
 * and passes it to the reduction rule so a red should throw a Conv
 * exception if it fails.
 *)
functor ConvUtil (structure Conv : CONV and Syntax : ABT where type t = Conv.term) : CONV_UTIL =
struct
  open Conv
  open Syntax
  structure Syntax = Syntax

  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t
  fun reductionRule red = red o map out o out
end
