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

exception Malformed of string
exception TODO of string

fun getD (t : term) =
  case out t of
      ` v => raise Malformed ("getD:var:" ^ Variable.toString v)
    | v \ x =>  raise Malformed ("getD:bterm:" ^ Syntax.toString t)
    | opr $ bs =>
      case DI.`<? opr of
	  SOME theta => (theta, bs)
	| NONE => raise Malformed "getD:NONE"

fun getC (t : term) =
  case out t of
      ` v => raise Malformed ("getD:var:" ^ Variable.toString v)
    | v \ x =>  raise Malformed ("getD:bterm:" ^ Syntax.toString t)
    | opr $ bs =>
      case CI.`<? opr of
	  SOME theta => (theta, bs)
	| NONE => raise Malformed "getC:NONE"

datatype proof = PROOF of {sequent : Sequent.sequent, extract : term, name : D.t, subproofs : proof list}
fun mk_proof seq ext name sub : proof =
  PROOF {sequent = seq, extract = ext, name = name, subproofs = sub}

val ax = CI.`> C.AX $$ #[]
val base = CI.`> C.BASE $$ #[]

fun term2Coq (t : term) : string =
  case out t of
      ` v => Variable.toString v
    | v \ t => raise Malformed "term2Coq:bterm"
    | opr $ bs =>
      case (CI.`<? opr, bs) of
	  (SOME C.AX, #[]) => "mk_axiom"
	| (SOME C.BASE, #[]) => "mk_base"
	| (SOME C.FIX, #[t]) => "(mk_fix " ^ term2Coq t ^ ")"
	| (SOME C.INL, #[t]) => "(mk_inl " ^ term2Coq t ^ ")"
	| (SOME C.INR, #[t]) => "(mk_inr " ^ term2Coq t ^ ")"
	| (SOME C.CEQUAL, #[t1,t2]) => "(mk_cequiv " ^ term2Coq t1 ^ " " ^ term2Coq t2 ^ ")"
	| (SOME C.APPROX, #[t1,t2]) => "(mk_approx " ^ term2Coq t1 ^ " " ^ term2Coq t2 ^ ")"
	| (SOME theta, _) => raise TODO ("term2Coq" ^ C.toString theta)
	| (NONE, _) => raise TODO "term2Coq:NONE"

fun context2Coq (c : context) : string =
  raise TODO "context2Coq"

(* coming from utils.fun *)
fun @@ (H, (x,A)) = Context.insert H x Visibility.Visible A
infix 8 @@

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
    | ((D.APPROX_EQ, #[e1, e2]), (C.EQ, #[t1, t2, T])) =>
      (case (getC t1, getC t2, getC T) of
	   ((C.APPROX, #[A1, B1]), (C.APPROX, #[A2, B2]), (C.UNIV i, #[])) =>
	   let val seq1 = H >> (into (CI.`> C.EQ $ #[A1, A1, base]))
	       val seq2 = H >> (into (CI.`> C.EQ $ #[B1, B2, base]))
	       val proof1 = build_proof seq1 e1
	       val proof2 = build_proof seq2 e2
	   in mk_proof seq ax D.APPROX_EQ [proof1, proof2]
	   end
	 | _ => raise Malformed "build_proof:APPROX_EQ:error")
    | ((D.ISECT_EQ, #[e1, ze2]), (C.EQ, #[t1, t2, T])) =>
      (case (out ze2, getC t1, getC t2, getC T) of
	   (z \ e2, (C.ISECT, #[A1, xB1]), (C.ISECT, #[A2, xB2]), (C.UNIV i, #[])) =>
	   let val seq1 = H >> (into (CI.`> C.EQ $ #[A1, A1, T]))
	       val seq2 = H @@ (z,A1) >> (into (CI.`> C.EQ $ #[xB1 // `` z, xB2 // `` z, T]))
	       val proof1 = build_proof seq1 e1
	       val proof2 = build_proof seq2 e2
	   in mk_proof seq ax D.ISECT_EQ [proof1, proof2]
	   end
	 | _ => raise Malformed "build_proof:ISECT_EQ:error")
    | ((D.BASE_MEMBER_EQ n, evs), (C.EQ, #[t1, t2, T])) =>
      (case getC T of
	   (C.BASE, #[]) =>
	   let val (ev :: evs) = Vector.foldr (fn (h,tl) => h :: tl) [] evs
	       val seq    = H >> (into (CI.`> C.CEQUAL $ #[t1, t2]))
	       val proof  = build_proof seq ev
	       val free   = Syntax.freeVariables t1
	       val proofs =
		   foldl (fn ((v, ev), proofs) =>
			     let val seq = H >> (into (CI.`> C.EQ $ #[``v, ``v, base]))
				 val proof = build_proof seq ev
			     in proofs @ [proof]
			     end)
			 []
			 (ListPair.zip (free, evs))
	   in mk_proof seq ax (D.BASE_MEMBER_EQ n) (proof :: proofs)
	   end
	 | _ => raise Malformed "build_proof:BASE_MEMBER_EQ:error")
    | ((D.ASSERT, #[e1, ze2]), _) =>
      let val z \ e2 = out ze2
	  val term = raise TODO ""
	  (* This term, the one we're asserted should be part of the evidence? *)
	  val seq1 = H >> term
	  val seq2 = H @@ (z,term) >> P
	  val PROOF proof1 = build_proof seq1 e1
	  val PROOF proof2 = build_proof seq2 e2
	  val ext = (#extract proof2) // (#extract proof1)
      in mk_proof seq ext D.ASSERT [PROOF proof1, PROOF proof2]
      end
    | ((theta, _), _) => raise TODO ("build_proof:" ^ D.toString theta ^ " " ^ Syntax.toString P)

fun proof2Coq (pr : proof) : string =
  case pr of
      PROOF {sequent = H >> P, extract, name = D.APPROX_REFL, subproofs = []} =>
      (case getC P of
	   (C.APPROX, #[t1, t2]) =>
	   if Syntax.eq (t1, t2)
	   then "(proof_approx_refl (" ^ term2Coq t1 ^ ") (" ^ context2Coq H ^ "))"
	   else raise Malformed "proof2Coq:APPROX_REFL:APPROX:diff"
	 | (theta, _) => raise Malformed ("proof2Coq:APPROX_REFL:" ^ C.toString theta))
    | PROOF {sequent = H >> P, extract, name = D.ISECT_EQ, subproofs = [prf1, prf2]} =>
      raise TODO "proof2Coq:ISECT_EQ"
    | PROOF {sequent = H >> P, extract, name, subproofs} =>
      raise TODO ("proof2Coq:" ^ D.toString name)

fun toCoq sequent evidence = proof2Coq (build_proof sequent evidence)

end
