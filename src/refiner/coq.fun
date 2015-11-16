functor Coq (structure Syntax : ABT_UTIL
	     structure Sequent : SEQUENT where type term = Syntax.t) : COQ =
struct

structure Syntax = Syntax

type term = Syntax.t

structure Sequent = Sequent
open Sequent
infix >>
open Syntax

exception Malformed

fun toCoq (seq : sequent) (evidence : term) =
  let val (H >> P) = seq
  in case out evidence of
	 ` v => raise Malformed
       | \ (v,t) => raise Malformed
       | $ (opr, bs) => ""
  end

end
