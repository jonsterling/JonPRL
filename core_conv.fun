functor CoreConv (CT : CONV_TYPES) : CORE_CONV =
struct
  open CT
  open Syntax
  infix $ \
  infix 8 $$ // \\

  fun CDEEP (c : conv) : conv = fn M =>
    c M handle _ =>
      case out M of
           O $ ES => O $$ (Vector.map (fn N => CDEEP c N handle _ => N) ES)
         | x \ E => x \\ CDEEP c E
         | ` x => `` x

  fun CTHEN (c1 : conv, c2 : conv) : conv = fn M =>
    c2 (c1 M)

  fun CTRY (c : conv) : conv = fn M =>
    c M handle _ => M

  fun CORELSE (c1 : conv, c2 : conv) : conv = fn M =>
    c1 M handle _ => c2 M

  val CID : conv = fn M => M
  val CFAIL : conv = fn M => raise Conv
end
