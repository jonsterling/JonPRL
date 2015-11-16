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

fun proof2Coq (seq : sequent) (evidence : term) =
  let val (H >> P) = seq
  in case out evidence of
	 ` v => raise Malformed
       | \ (v,t) => raise Malformed
       | $ (opr, bs) =>
	 (case (Syntax.Operator.toString opr, bs, out P) of
	      ("approx-refl", #[], $ (apr, #[t1, t2])) =>
	      if Syntax.Operator.toString apr = "approx" andalso Syntax.eq (t1, t2)
	      then "(proof_approx_refl ?a ?H)" (* ?a is t1 and ?H is H *)
	      else raise Malformed
	   | _ => raise Malformed)
  end

val toCoq = proof2Coq

end
