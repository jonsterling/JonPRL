structure DevelopmentAstEval :
          sig
              val eval : Development.t
                         -> DevelopmentAst.t list
                         -> Development.t
          end =
struct
  open DevelopmentAst
  fun eval_decl D ast =
    case ast of
        THEOREM (lbl, term, tac) =>
        Development.prove D (lbl,
                             Sequent.>> (Sequent.Context.empty, term),
                             TacticEval.eval D tac)
      | OPERATOR (lbl, arity) => D
      | TACTIC (lbl, tac) =>
        Development.defineTactic D (lbl, TacticEval.eval D tac)
      | DEFINITION (pat, term) =>
        Development.defineOperator D {definiendum = pat,
                                      definiens = term}

  fun eval D = List.foldl (fn (decl, D) => eval_decl D decl) D
end
