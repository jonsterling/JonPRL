structure DevelopmentAstEval :
sig
  val eval : Development.world -> DevelopmentAst.t list -> bool -> Development.world
end =
struct
  open DevelopmentAst
  exception Open of Syntax.t

  structure SmallStep = SmallStepUtil (SmallStep (Syntax))

  val operatorToLabel = Syntax.Operator.toString

  fun evalCommand D cmd =
    case cmd of
         PRINT theta =>
         let
           open Development
           val lbl = operatorToLabel theta
           val declString =
             case SOME (lookupObject D theta) handle _ => NONE of
                  SOME obj => Object.toString (lbl, obj)
                | NONE => "Operator " ^ lbl ^ " : " ^ Arity.toString (Syntax.Operator.arity theta) ^ "."
         in
           print ("\n" ^ declString ^ "\n"); D
         end
       | EVAL (M, gas) =>
         let
           fun termString M = "⸤" ^ Syntax.toString M ^ "⸥"
           val result = Sum.INR (SmallStep.steps (M, gas)) handle SmallStep.Stuck R => Sum.INL R
         in
           case result of
               Sum.INR (M',n) => print ("\n" ^ termString M ^ " ⇒ " ^ termString M' ^ " in " ^ Int.toString n ^ " steps.\n")
             | Sum.INL R => print ("\n" ^ termString M ^ " gets stuck at " ^ termString R ^ ".\n");
            D
         end
       | SEARCH oper =>
         let
           open Development
           val lbl = operatorToLabel oper
           val results = searchObject D lbl
         in
           print ("\nResults for " ^ lbl ^ ":\n");
           List.app
             (fn (lbl, obj) => print ("\n" ^ Object.toString (lbl, obj) ^ "\n"))
             results;
           D
         end
       | ADD_RESOURCE (r, t) => Development.addResource D (r, TacticEval.eval D t)
       | NEW_RESOURCE r => Development.declareResource D r

  fun evalDecl D ast =
    case ast of
        THEOREM (lbl, theta, term, tac) =>
        let
          val vars = Syntax.freeVariables term
          val () =
              case vars of
                  [] => ()
                | _ => raise Open term
	in Development.prove D
			     (lbl, theta,
			      Sequent.>> (Sequent.Context.empty, term),
			      TacticEval.eval D tac)
	end
      | OPERATOR (lbl, theta) =>
        Development.declareOperator D (lbl, theta)
      | TACTIC (lbl, tac) =>
        Development.defineTactic D (lbl, fn D => TacticEval.eval D tac)
      | DEFINITION (pat, term) =>
        Development.defineOperator D {definiendum = pat, definiens = term}
      | NOTATION (notation, theta) =>
        Development.declareNotation D (theta, notation)
      | COMMAND cmd => evalCommand D cmd

  fun export2Coq n [] = ()
    | export2Coq n ((opr, stmt, ev) :: l) =
      let val name  = "/tmp/tocoq" ^ Int.toString n ^ ".v"
	  val _     = print ("[exporting " ^ opr ^ " lemma to " ^ name ^ "]\n")
	  val stout = TextIO.openOut name
	  val _     = TextIO.output (stout, "Require Export proof.\n\n")
	  val _     = TextIO.output (stout, "Lemma " ^ opr ^ " {o} :\n")
	  val _     = TextIO.output (stout, "  @sequent_true2 o emlib (" ^ stmt ^ ").\n")
	  val _     = TextIO.output (stout, "Proof.\n")
	  val _     = TextIO.output (stout, " apply valid_proof;\n")
	  val _     = TextIO.output (stout, " [ exact (eq_refl, (eq_refl, eq_refl))\n")
	  val _     = TextIO.output (stout, " | exact " ^ ev ^ "\n")
	  val _     = TextIO.output (stout, " ].\n")
	  val _     = TextIO.output (stout, "Qed.\n\n")
	  val _     = TextIO.output (stout, "(*\n")
	  val _     = TextIO.output (stout, "*** Local Variables:\n")
	  val _     = TextIO.output (stout, "*** coq-load-path: (\"util\" \"terms\" \"computation\" \"cequiv\" \"close\" \"per\" \"rules\")\n")
	  val _     = TextIO.output (stout, "*** End:\n")
	  val _     = TextIO.output (stout, "*)\n")
      in export2Coq (n + 1) l
      end

  fun toCoq world =
    let val str1  = Development.world2string world
	val lst   = Development.world2Coq world
	val stout = TextIO.openOut "/tmp/jonprl"
	val _     = TextIO.output (stout, str1)
	val _     = export2Coq 1 lst
    in ()
    end


  fun eval D ast tocoq =
    let val world : Development.world = List.foldl (fn (decl, D) => evalDecl D decl) D ast
	val _ = if tocoq then toCoq world else ()
    in world
    end
end
