functor DevelopmentParser
  (structure Tactic : TACTIC
   structure DevelopmentAst : DEVELOPMENT_AST
     where type Tactic.t = Tactic.t
   structure Syntax : PARSE_ABT
     where type ParseOperator.world = ParserContext.world
     where type t = DevelopmentAst.Syntax.t
     where type Operator.t = DevelopmentAst.Syntax.Operator.t

   structure TacticScript : TACTIC_SCRIPT
     where type tactic = Tactic.t
     where type world = ParserContext.world
   ) : DEVELOPMENT_PARSER =
struct
  open ParserContext

  structure DevelopmentAst = DevelopmentAst

  open ParserCombinators CharParser
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >> --

  structure TP = TokenParser
    (open JonprlLanguageDef
     val reservedNames = ["Theorem",
                          "Tactic",
                          "Operator",
                          "Print",
                          "Eval",
                          "Search",
                          "Resource",
                          "Declare"])
  open TP

  (* Make sure that our version of braces smartly handles whitespace *)
  val braces = fn p => braces (spaces >> p << spaces)

  fun parseTm fvs w =
    squares (Syntax.parseAbt w (Syntax.initialState fvs))

  val parseOperator = Syntax.ParseOperator.parseOperator

  val parsePattern = parseTm []

  val parseName =
    identifier
      wth Syntax.Variable.named

  val parseLabel = identifier

  fun parseTheorem w =
    reserved "Theorem" >> parseLabel << colon
      && parseTm [] w
      && braces (!! (TacticScript.parse w))
      wth (fn (lbl, (M, (tac, pos))) =>
             let
               val w' = declareOperator w (lbl, #[])
               val (theta, _) = lookupOperator w' lbl
             in
               (w', DevelopmentAst.THEOREM (lbl, theta, M, Tactic.COMPLETE (tac, {name = "COMPLETE", pos = pos})))
             end)

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parseArity =
    parens (semiSep parseInt)
    wth Vector.fromList

  fun parseTactic w =
    reserved "Tactic" >> parseLabel
      && braces (TacticScript.parse w)
      wth (fn (lbl, tac) =>
              (w, DevelopmentAst.TACTIC (lbl, tac)))

  fun parseOperatorDecl w =
    (reserved "Operator" >> parseLabel << colon && parseArity)
     wth (fn (lbl, arity) =>
           let
             val w' = declareOperator w (lbl, arity)
             val (theta, _) = lookupOperator w' lbl
           in
             (w', DevelopmentAst.OPERATOR (lbl, theta))
           end)

  fun parseNotationDecl w =
    Notation.parse && (symbol ":=" >> parseOperator w)
    wth (fn (notation, theta) =>
              (declareNotation w (theta, notation), DevelopmentAst.NOTATION (notation, theta)))

  fun parseOperatorDef w =
    parsePattern w -- (fn pat =>
      succeed pat && (symbol "=def=" >> parseTm (Syntax.freeVariables pat) w)
    ) wth (fn (P : Syntax.t, N : Syntax.t) =>
              (w, DevelopmentAst.DEFINITION (P, N)))

  fun parsePrint (w : world) =
    reserved "Print" >>
      parseOperator w
      wth (fn oper => (w, DevelopmentAst.PRINT oper))

  fun parseEval w =
    reserved "Eval" >>
      opt parseInt << spaces && parseTm [] w
      wth (fn (gas, M) => (w, DevelopmentAst.EVAL (M, gas)))

  fun parseSearch w =
    reserved "Search" >>
      parseOperator w
      wth (fn oper => (w, DevelopmentAst.SEARCH oper))

  fun parseAddResource w =
    (reserved "Resource" >> Resource.parse (ParserContext.lookupResource w)) &&
      (spaces >> string "+=" >> spaces >> braces (TacticScript.parse w))
      wth (fn pair => (w, DevelopmentAst.ADD_RESOURCE pair))

  fun parseNewResource w =
    reserved "Declare" >> identifier
             wth (fn id =>
                    let
                      val w' = declareResource w id
                    in
                      (w', DevelopmentAst.NEW_RESOURCE (lookupResource w' id))
                    end)

  fun parseCommand w =
    (parsePrint w
       || parseEval w
       || parseSearch w
       || parseNewResource w
       || parseAddResource w)
    wth (fn (w', cmd) => (w', DevelopmentAst.COMMAND cmd))

  fun parseDecl w =
      parseTheorem w
      || parseTactic w
      || parseOperatorDecl w
      || parseOperatorDef w
      || parseNotationDecl w
      || parseCommand w

  fun parse' w ast () =
    whiteSpace >>
    (parseDecl w << dot) -- (fn (w', decl) =>
      $ (parse' w' (decl :: ast)) <|>
      (whiteSpace >> not any) return (w', decl :: ast))

  fun parse w = $ (parse' w []) wth (fn (w, ast) => (w, List.rev ast))
end

structure CttDevelopmentParser = DevelopmentParser
  (structure Syntax = Syntax
   structure Tactic = Tactic
   structure DevelopmentAst = DevelopmentAst
   structure TacticScript = TacticScript)
