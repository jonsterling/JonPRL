structure DevelopmentAstEval :
sig
  val eval : Development.world -> DevelopmentAst.t list -> Development.world
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
             case SOME (lookupObject D lbl) handle _ => NONE of
                  SOME obj => Object.toString (lbl, obj)
                | NONE => "Operator " ^ lbl ^ " : " ^ Arity.toString (Syntax.Operator.arity theta) ^ "."
         in
           print ("\n" ^ declString ^ "\n")
         end
       | EVAL (M, gas) =>
         let
           fun termString M = "⸤" ^ Syntax.toString M ^ "⸥"
           val result = Sum.INR (SmallStep.steps (M, gas)) handle SmallStep.Stuck R => Sum.INL R
         in
           case result of
                Sum.INR (M',n) => print ("\n" ^ termString M ^ " ⇒ " ^ termString M' ^ " in " ^ Int.toString n ^ " steps.\n")
              | Sum.INL R => print ("\n" ^ termString M ^ " gets stuck at " ^ termString R ^ ".\n")
         end

  fun evalDecl D ast =
    case ast of
        THEOREM (lbl, term, tac) =>
        let
          val vars = Syntax.freeVariables term
          val () =
              case vars of
                  [] => ()
                | _ => raise Open term
        in
          Development.prove D (lbl,
                               Sequent.>> (Sequent.Context.empty, term),
                               TacticEval.eval D tac)
        end
      | OPERATOR (lbl, arity) =>
        Development.declareOperator D (lbl, arity)
      | TACTIC (lbl, tac) =>
        Development.defineTactic D (lbl, TacticEval.eval D tac)
      | DEFINITION (pat, term) =>
        Development.defineOperator D {definiendum = pat, definiens = term}
      | COMMAND cmd =>
        (evalCommand D cmd; D)

  fun eval D = List.foldl (fn (decl, D) => evalDecl D decl) D
end
