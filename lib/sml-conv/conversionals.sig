(* This the payoff for creating a CONV ascribing structure. This signature
 * specifies several "generic" conversions as well as ways to combine
 * existing ones.
 *)
signature CONVERSIONALS =
sig
  type conv

  (* CID is the conversion which always succeeds but does nothing.
   * It simply returns the supplied term with no modifications
   *)
  val CID : conv

  (* CTHEN (t1, t2) run t1 to it and then run t2 to the result.
   * If either fail the entire conv will fail.
   *)
  val CTHEN : conv * conv -> conv

  (* This takes a term and fails immediately regardless of the term.
   * It's an annihilator for CTHEN.
   *)
  val CFAIL : conv

  (* CORElSE (t1, t2) will run t1 and if it succeeds it will
   * return the result. If t1 instead fails it will run t2 as if
   * it had never run t1. This means if this conv fails it will display
   * t2's exception.
   *)
  val CORELSE : conv * conv -> conv

  (* [This conversion only makes sense when the underlying term
   *  is a tree]
   *
   * CDEEP t will run t from the bottom up. If [t] can be applied to
   * any subterm it will be. This means that whenever [t] is run on a term
   * [t] has already been run on the subterms of that term.
   *)
  val CDEEP : conv -> conv

  (* CTRY t will attempt to run t and if it fails behave as CID.
   * Thus CTRY t will never fail regardless of t
   *)
  val CTRY : conv -> conv
end
