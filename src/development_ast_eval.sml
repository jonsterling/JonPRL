structure DevelopmentAstEval :
sig
  val eval : Development.world -> DevelopmentAst.t list -> Development.world
end =
struct
  open DevelopmentAst
  exception Open of Syntax.t

  fun evalCommand D cmd =
    case cmd of
         PRINT lbl =>
         let
           open Development
           val object = lookupObject D lbl
           val declString = Object.toString (lbl, object)
         in
           print ("\n" ^ declString ^ "\n"); D
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
        evalCommand D cmd

  fun eval D = List.foldl (fn (decl, D) => evalDecl D decl) D
end
