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

(* args is used for extra arguments, such as for the Hypothesis rule, we need to point to
 * an hypothesis name *)
datatype proof = PROOF of {sequent : Sequent.sequent, extract : term, name : D.t, args : term list, subproofs : proof list}
fun mk_proof seq ext name args sub : proof =
  PROOF {sequent = seq, extract = ext, name = name, args = args, subproofs = sub}

fun proof_name (PROOF prf) = #name prf
fun proof_ext (PROOF prf) = #extract prf

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
	| (SOME C.LAM, #[xt]) =>
	  let val x \ t = out xt
	  in "(mk_lam " ^ Variable.toString x ^ " " ^ term2Coq t ^ ")"
	  end
	| (SOME theta, _) => raise TODO ("term2Coq:" ^ C.toString theta)
	| (NONE, _) => raise TODO "term2Coq:NONE"

fun splitContext _ [] = ([], NONE, [])
  | splitContext z ((name,vis,term) :: rest) =
    if Variable.eq (z,name)
    then ([], SOME (name,vis,term), rest)
    else let val (l1,x,l2) = splitContext z rest
	 in ((name,vis,term) :: l1, x, l2)
	 end

fun context2Coq' c : string =
  foldr (fn ((name,Visibility.Visible,term), ctxt) => "(cons (mk_hyp "  ^ Variable.toString name ^ " " ^ term2Coq term ^ ") " ^ ctxt ^ ")"
  	  | ((name,Visibility.Hidden,term),  ctxt) => "(cons (mk_hhyp " ^ Variable.toString name ^ " " ^ term2Coq term ^ ") " ^ ctxt ^ ")")
	"nil"
	c

fun context2Coq (c : context) : string = context2Coq' (Context.listItems c)

(* coming from utils.fun *)
fun @@ (H, (x,A)) = Context.insert H x Visibility.Visible A
infix 8 @@

structure Conv = Conv(Syntax)
structure Conversionals = Conversionals (structure Syntax = Syntax structure Conv = Conv)

fun build_proof (seq as (H >> P) : sequent) (evidence : term) : proof =
  case (getD evidence, getC P) of
      ((D.APPROX_REFL, #[]), _) => mk_proof seq ax D.APPROX_REFL [] []

    | ((D.CEQUAL_APPROX, #[e1, e2]), (C.CEQUAL, #[t1, t2])) =>
      let val seq1 = H >> (into (CI.`> C.APPROX $ #[t1, t2]))
	  val seq2 = H >> (into (CI.`> C.APPROX $ #[t2, t1]))
	  val proof1 = build_proof seq1 e1
	  val proof2 = build_proof seq2 e2
      in mk_proof seq ax D.CEQUAL_APPROX [] [proof1, proof2]
      end

    | ((D.APPROX_EQ, #[e1, e2]), (C.EQ, #[t1, t2, T])) =>
      (case (getC t1, getC t2, getC T) of
	   ((C.APPROX, #[A1, B1]), (C.APPROX, #[A2, B2]), (C.UNIV i, #[])) =>
	   let val seq1 = H >> (into (CI.`> C.EQ $ #[A1, A1, base]))
	       val seq2 = H >> (into (CI.`> C.EQ $ #[B1, B2, base]))
	       val proof1 = build_proof seq1 e1
	       val proof2 = build_proof seq2 e2
	   in mk_proof seq ax D.APPROX_EQ [] [proof1, proof2]
	   end
	 | _ => raise Malformed "build_proof:APPROX_EQ:error")

    | ((D.ISECT_EQ, #[e1, ze2]), (C.EQ, #[t1, t2, T])) =>
      (case (out ze2, getC t1, getC t2, getC T) of
	   (z \ e2, (C.ISECT, #[A1, xB1]), (C.ISECT, #[A2, xB2]), (C.UNIV i, #[])) =>
	   let val seq1 = H >> (into (CI.`> C.EQ $ #[A1, A1, T]))
	       val seq2 = H @@ (z,A1) >> (into (CI.`> C.EQ $ #[xB1 // `` z, xB2 // `` z, T]))
	       val proof1 = build_proof seq1 e1
	       val proof2 = build_proof seq2 e2
	   in mk_proof seq ax D.ISECT_EQ [`` z] [proof1, proof2]
	   end
	 | _ => raise Malformed "build_proof:ISECT_EQ:error")

    | ((D.BASE_MEMBER_EQ n, evs), (C.EQ, #[t1, t2, T])) =>
      (case getC T of
	   (C.BASE, #[]) =>
	   let val (ev1 :: evs) = Vector.foldr (fn (h,tl) => h :: tl) [] evs
	       val seq1   = H >> (into (CI.`> C.CEQUAL $ #[t1, t2]))
	       val proof1 = build_proof seq1 ev1
	       val free   = Syntax.freeVariables t1
	       val proofs =
		   foldl (fn ((v, ev), proofs) =>
			     let val seq = H >> (into (CI.`> C.EQ $ #[``v, ``v, base]))
				 val proof = build_proof seq ev
			     in proofs @ [proof]
			     end)
			 []
			 (ListPair.zip (free, evs))
	   in mk_proof seq ax (D.BASE_MEMBER_EQ n) [] (proof1 :: proofs)
	   end
	 | _ => raise Malformed "build_proof:BASE_MEMBER_EQ:error")

    | ((D.ASSERT, #[term, e1, ze2]), _) =>
      let val z \ e2 = out ze2
	  val seq1 = H >> term
	  val seq2 = H @@ (z,term) >> P
	  val proof1 = build_proof seq1 e1
	  val proof2 = build_proof seq2 e2
	  val ext = (into (z \ (proof_ext proof2))) // (proof_ext proof1)
      in mk_proof seq ext D.ASSERT [`` z, term] [proof1, proof2]
      end

    | ((D.CEQUAL_SUBST, #[M, N, e1, e2]), _) =>
      let val P' = Conversionals.CDEEP (fn M' => if Syntax.eq (M,M') then N else raise Conv.Conv) P
	  val seq1 = H >> into (CI.`> C.CEQUAL $ #[M, N])
	  val seq2 = H >> P'
	  val proof1 = build_proof seq1 e1
	  val proof2 = build_proof seq2 e2
	  val ext = proof_ext proof2
      in mk_proof seq ext D.CEQUAL_SUBST [M, N] [proof1, proof2]
      end

    | ((D.ASSUME_HAS_VALUE, #[ze1, e2]), (C.APPROX, #[M, _])) =>
      let val z \ e1 = out ze1
          val v = Variable.named "_"
	  val hv = into (CI.`> C.APPROX $ #[ax, CI.`> C.CBV $$ #[M,v \\ ax]])
	  val uni = into (CI.`> (C.UNIV Level.base) $ #[]) (* When would level 0 be not enough? *)
	  val mem = into (CI.`> C.EQ $ #[hv, hv, uni])
	  val seq1 = H @@ (z,hv) >> P
	  val seq2 = H >> mem
	  val proof1 = build_proof seq1 e1
	  val proof2 = build_proof seq2 e2
      in mk_proof seq ax D.ASSUME_HAS_VALUE [`` z] [proof1, proof2]
      end

    | ((D.HYPOTHESIS, #[V]), _) => mk_proof seq V D.HYPOTHESIS [] []

    | ((D.BOTTOM_DIVERGES, #[V]), _) => mk_proof seq ax D.BOTTOM_DIVERGES [V] []

    | ((theta, _), _) => raise TODO ("build_proof:" ^ D.toString theta ^ " " ^ Syntax.toString P)

fun proof2Coq (pr : proof) : string =
  case pr of
      PROOF {sequent = H >> P, extract, name = D.APPROX_REFL, args, subproofs = []} =>
      (case getC P of
	   (C.APPROX, #[t1, t2]) =>
	   if Syntax.eq (t1, t2)
	   then "(proof_approx_refl (" ^ term2Coq t1 ^ ") (" ^ context2Coq H ^ "))"
	   else raise Malformed "proof2Coq:APPROX_REFL:APPROX:diff"
	 | (theta, _) => raise Malformed ("proof2Coq:APPROX_REFL:" ^ C.toString theta))

    | PROOF {sequent = H >> P, extract, name = D.ISECT_EQ, args = [Z], subproofs = [prf1, prf2]} =>
      let val p1 = proof2Coq prf1
	  val p2 = proof2Coq prf2
	  val (C.EQ, #[t1, t2, U]) = getC P
	  val (C.ISECT, #[A1, xB1]) = getC t1
	  val (C.ISECT, #[A2, xB2]) = getC t2
	  val (C.UNIV i, #[]) = getC U
	  val x1 \ B1 = out xB1
	  val x2 \ B2 = out xB2
	  val ` z = out Z
      in "(proof_isect_eq"
	 ^ " (" ^ term2Coq A1 ^ ")"
	 ^ " (" ^ term2Coq A2 ^ ")"
	 ^ " (" ^ term2Coq B1 ^ ")"
	 ^ " (" ^ term2Coq B2 ^ ")"
	 ^ " (" ^ Variable.toString x1 ^ ")"
	 ^ " (" ^ Variable.toString x2 ^ ")"
	 ^ " (" ^ Variable.toString z ^ ")"
	 ^ " (" ^ Level.toString i ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " eq_refl"
	 ^ " " ^ p1
	 ^ " " ^ p2
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.APPROX_EQ, args, subproofs = [prf1, prf2]} =>
      let val p1 = proof2Coq prf1
	  val p2 = proof2Coq prf2
	  val (C.EQ, #[t1, t2, U]) = getC P
	  val (C.APPROX, #[A1, B1]) = getC t1
	  val (C.APPROX, #[A2, B2]) = getC t2
	  val (C.UNIV i, #[]) = getC U
      in "(proof_approx_eq"
	 ^ " (" ^ term2Coq A1 ^ ")"
	 ^ " (" ^ term2Coq A2 ^ ")"
	 ^ " (" ^ term2Coq B1 ^ ")"
	 ^ " (" ^ term2Coq B2 ^ ")"
	 ^ " (" ^ Level.toString i ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " " ^ p1
	 ^ " " ^ p2
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.BASE_MEMBER_EQ n, args, subproofs = prf1 :: prfs} =>
      let val p1 = proof2Coq prf1
	  val ps = List.map proof2Coq prfs
	  val (C.EQ, #[t1, t2, B]) = getC P
	  val (C.BASE, #[]) = getC B
	  val free = Syntax.freeVariables t1
      in "(proof_base_member_eq"
	 ^ " (" ^ term2Coq t1 ^ ")"
	 ^ " (" ^ term2Coq t2 ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " " ^ p1
	 ^ " " ^ "(Llist_implies_forall (" ^ foldr (fn (p, str) => "(lcons " ^ p ^ " " ^ str ^ ")") "lnil" ps ^ "))"
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.CEQUAL_APPROX, args, subproofs = [prf1, prf2]} =>
      let val p1 = proof2Coq prf1
	  val p2 = proof2Coq prf2
	  val (C.CEQUAL, #[t1, t2]) = getC P
      in "(proof_cequiv_approx"
	 ^ " (" ^ term2Coq t1 ^ ")"
	 ^ " (" ^ term2Coq t2 ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " " ^ p1
	 ^ " " ^ p2
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.ASSERT, args = [Z, C], subproofs = [prf1, prf2]} =>
      let val p1 = proof2Coq prf1
	  val p2 = proof2Coq prf2
	  val ` z = out Z
      in "(proof_cut"
	 ^ " (" ^ term2Coq C ^ ")"
	 ^ " (" ^ term2Coq P ^ ")"
	 ^ " (" ^ term2Coq (proof_ext prf2) ^ ")"
	 ^ " (" ^ term2Coq (proof_ext prf1)  ^ ")"
	 ^ " (" ^ Variable.toString z  ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " " ^ p1
	 ^ " " ^ p2
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.HYPOTHESIS, args, subproofs} =>
      let val ` z = out extract
	  val lst = Context.listItems H
	  (* vis is supposed to be Visible and term is supposed to be P *)
	  val (l1, SOME (name,vis,term), l2) = splitContext z lst
      in "(proof_hypothesis"
	 ^ " (" ^ term2Coq extract  ^ ")"
	 ^ " (" ^ term2Coq P ^ ")"
	 ^ " (" ^ context2Coq' l1 ^ ")"
	 ^ " (" ^ context2Coq' l2 ^ ")"
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.CEQUAL_SUBST, args = [M, N], subproofs = [prf1, prf2]} =>
      let val p1 = proof2Coq prf1
	  val p2 = proof2Coq prf2
	  val v = Variable.named "v"
	  val P' = Conversionals.CDEEP (fn M' => if Syntax.eq (M,M') then `` v else raise Conv.Conv) P
      in "(proof_cequiv_subst_concl"
	 ^ " (" ^ term2Coq P' ^ ")"
	 ^ " (" ^ Variable.toString v ^ ")"
	 ^ " (" ^ term2Coq M ^ ")"
	 ^ " (" ^ term2Coq N ^ ")"
	 ^ " (" ^ term2Coq (proof_ext prf2) ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " eq_refl eq_refl eq_refl eq_refl"
	 ^ " " ^ p2
	 ^ " " ^ p1
	 ^ ")"
      end

    | PROOF {sequent = H >> P, extract, name = D.ASSUME_HAS_VALUE, args = [Z], subproofs = [prf1, prf2]} =>
      let val p1 = proof2Coq prf1
	  val p2 = proof2Coq prf2
	  val ` z = out Z
      in raise TODO "proof2Coq:ASUME_HAS_VALUE" (*"(proof_assume_has_value"
	 ^ " (" ^ term2Coq P' ^ ")"
	 ^ " (" ^ Variable.toString v ^ ")"
	 ^ " (" ^ term2Coq M ^ ")"
	 ^ " (" ^ term2Coq N ^ ")"
	 ^ " (" ^ term2Coq (proof_ext prf2) ^ ")"
	 ^ " (" ^ context2Coq H ^ ")"
	 ^ " eq_refl eq_refl eq_refl eq_refl"
	 ^ " " ^ p2
	 ^ " " ^ p1
	 ^ ")"*)
      end

    | PROOF {sequent = H >> P, extract, name, args, subproofs} =>
      raise TODO ("proof2Coq:" ^ D.toString name)

fun toCoq sequent evidence =
  let val proof = build_proof sequent evidence
  in proof2Coq proof
  end

end
