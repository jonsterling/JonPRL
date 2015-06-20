functor Conversionals (structure Conv : CONV and Syntax : ABT where type t = Conv.term) : CONVERSIONALS =
struct
  open Conv
  open Syntax

  infix $ \
  infix 8 $$ \\

  fun CDEEP (c : conv) : conv = fn M =>
    c M handle _ =>
      case out M of
          (* If we're at an operator, map a recursive call over all
           * subterms.
           *)
           O $ ES => into (O $ (Vector.map (fn N => CDEEP c N) ES))
         (* If we're at a binding site, recurse under the binder *)
         | x \ E => into (x \ CDEEP c E)
         (* If we're at a variable, just give up *)
         | ` x => into (` x)

  fun CTHEN (c1 : conv, c2 : conv) : conv = fn M =>
    c2 (c1 M)

  fun CTRY (c : conv) : conv = fn M =>
    c M handle _ => M

  fun CORELSE (c1 : conv, c2 : conv) : conv = fn M =>
    c1 M handle _ => c2 M

  val CID : conv = fn M => M
  val CFAIL : conv = fn M => raise Conv
end
