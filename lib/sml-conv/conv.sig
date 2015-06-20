(* This signature should be implemented by any system planning on
 * using this library. It just describes the terms in the system
 * as well as the exception to be raised by a failing conversion.
 *)
signature CONV =
sig
  (* The type of things we're converting between *)
  type term

  (* A conv is a function between two terms. It may be
   * a partial function if the conversion is not
   * applicable to all terms in which case it should
   * raise the Conv exception
   *)
  type conv = term -> term
  exception Conv
end

(* As a super set of the CONV signature this when
 * the term type is actually built from an ABT (in the sense
 * of (sml-abt) additional functions are possible.
 *)
signature CONV_UTIL =
sig
  (* This is a strict superset of CONV *)
  include CONV
  (* We require there be an ABT module where
   * term (from CONV) is the type of the ABT
   *)
  structure Syntax : ABT where type t = term

  (* A red (short for reduction) is a rule taking a partially
   * unfolded term and collapsing it back into a term.
   *)
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  (* Given a reduction rule we can construct a conv. If called
   * on a term which cannot be reduced by the provided reduction
   * rule this should raise a Conv exception
   *)
  val reductionRule : red -> conv
end
