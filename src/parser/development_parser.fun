signature PARSE_CTT =
  PARSE_ABT
    where type Operator.t = string OperatorType.operator
    where type ParseOperator.world = StringVariableContext.world

functor DevelopmentParser
  (structure ParserContext : PARSER_CONTEXT
   structure Tactic : TACTIC
     where type label = ParserContext.label
   structure DevelopmentAst : DEVELOPMENT_AST
     where type Tactic.t = Tactic.t
     where type label = ParserContext.label
   structure Syntax : PARSE_ABT
     where type ParseOperator.world = ParserContext.world
     where type t = DevelopmentAst.Syntax.t
     where type Operator.t = DevelopmentAst.Syntax.Operator.t

   structure TacticScript : TACTIC_SCRIPT
     where type tactic = Tactic.t
     where type world = ParserContext.world

   val operatorToLabel : Syntax.Operator.t -> ParserContext.label
   val stringToLabel : string -> Tactic.label) : DEVELOPMENT_PARSER =
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
     val reservedNames = ["Theorem", "Tactic", "Operator", "Print", "Eval"])
  open TP

  fun parseTm fvs w =
    squares (Syntax.parseAbt w (Syntax.initialState fvs))

  val parseOperator = Syntax.ParseOperator.parseOperator

  val parsePattern = parseTm []

  val parseName =
    identifier
      wth Syntax.Variable.named

  val parseLabel = identifier wth stringToLabel

  fun parseTheorem w =
    reserved "Theorem" >> parseLabel << colon
      && parseTm [] w
      && braces (!! (TacticScript.parse w))
      wth (fn (thm, (M, (tac, pos))) =>
             (declareOperator w (thm, #[]), DevelopmentAst.THEOREM
               (thm, M, Tactic.COMPLETE (tac, {name = "COMPLETE", pos = pos}))))

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
             (declareOperator w (lbl, arity),
              DevelopmentAst.OPERATOR (lbl, arity)))

  fun parseNotationDecl w =
    Notation.parse && (symbol "=def=" >> parseOperator w)
    wth (fn (notation, theta) =>
              (declareNotation w (operatorToLabel theta, notation), DevelopmentAst.NOTATION (notation, theta)))

  fun parseOperatorDef w =
    parsePattern w -- (fn pat =>
      succeed pat && (symbol "=def=" >> parseTm (Syntax.freeVariables pat) w)
    ) wth (fn (P : Syntax.t, N : Syntax.t) =>
              (w, DevelopmentAst.DEFINITION (P, N)))

  fun parsePrint (w : world) =
    reserved "Print" >>
      parseOperator w
      wth DevelopmentAst.PRINT

  fun parseEval w =
    reserved "Eval" >>
      opt parseInt << spaces && parseTm [] w
      wth (fn (gas, M) => DevelopmentAst.EVAL (M, gas))

  fun parseCommand w =
    (parsePrint w || parseEval w)
    wth (fn cmd => (w, DevelopmentAst.COMMAND cmd))

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
   structure TacticScript = CttScript
   val stringToLabel = StringVariable.named
   val operatorToLabel = Syntax.Operator.toString
   structure ParserContext = StringVariableContext)
