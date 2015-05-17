signature CONTEXT_UTIL =
sig
  include CONTEXT
  structure Syntax : ABT_UTIL

  val is_irrelevant : Syntax.t context * name -> bool
end
