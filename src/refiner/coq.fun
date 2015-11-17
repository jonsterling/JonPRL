functor Coq (structure Syntax : ABT_UTIL where type Operator.t = UniversalOperator.t
	     structure Sequent : SEQUENT where type term = Syntax.t where Context.Syntax = Syntax) : COQ =
struct

structure Syntax = Syntax

type term = Syntax.t

structure Sequent = Sequent
open Sequent
infix >>

open Syntax
infix $ \ $$ \\ //

structure D  = Derivation
structure DI = DerivationInj
structure C  = CttCalculus
structure CI = CttCalculusInj

exception Malformed
exception TODO

fun getD (t : term) =
  case out t of
      ` v => raise Malformed
    | v \ t =>  raise Malformed
    | opr $ bs =>
      case DI.`<? opr of
	  SOME theta => (theta, bs)
       |  _ => raise Malformed

fun getC (t : term) =
  case out t of
      ` v => raise Malformed
    | v \ t =>  raise Malformed
    | opr $ bs =>
      case CI.`<? opr of
	  SOME theta => (theta, bs)
       |  _ => raise Malformed

datatype proof = PROOF of {sequent : Sequent.sequent, extract : term, name : D.t, subproofs : proof list}
fun mk_proof seq ext name sub : proof =
  PROOF {sequent = seq, extract = ext, name = name, subproofs = sub}

val ax = CI.`> C.AX $$ #[]

fun build_proof (seq as (H >> P) : sequent) (evidence : term) : proof =
  case (getD evidence, getC P) of
      ((D.APPROX_REFL, #[]), _) => mk_proof seq ax D.APPROX_REFL []
    | ((D.CEQUAL_APPROX, #[e1, e2]), (C.CEQUAL, #[t1, t2])) =>
      let val seq1 = H >> (into (CI.`> C.APPROX $ #[t1, t2]))
	  val seq2 = H >> (into (CI.`> C.APPROX $ #[t2, t1]))
	  val proof1 = build_proof seq1 e1
	  val proof2 = build_proof seq2 e2
      in mk_proof seq ax D.CEQUAL_APPROX [proof1, proof2]
      end
    | _ => raise TODO

fun proof2Coq (pr : proof) : string =
  case pr of
      PROOF {sequent = H >> P, extract, name = D.APPROX_REFL, subproofs = []} =>
      (case getC P of
	   (C.APPROX, #[t1, t2]) =>
	   if Syntax.eq (t1, t2)
	   then "(proof_approx_refl ?a ?H)" (* ?a is t1 and ?H is H *)
	   else raise Malformed
	 | _ => raise Malformed)
    | _ => raise TODO

fun toCoq seq evidence = proof2Coq (build_proof seq evidence)

end
