signature PARSE_CTT =
  PARSE_ABT
    where type Operator.t = string OperatorType.operator
    where type ParseOperator.world = string -> Arity.t

functor DevelopmentParser
  (structure ParserContext : PARSER_CONTEXT
   structure Tactic : TACTIC
     where type label = ParserContext.label
   structure Syntax : PARSE_ABT
     where type ParseOperator.world = Tactic.label -> Arity.t
   structure DevelopmentAst : DEVELOPMENT_AST
     where type Syntax.t = Syntax.t
     where type Tactic.t = Tactic.t
     where type label = ParserContext.label

   structure TacticScript : TACTIC_SCRIPT
     where type tactic = Tactic.t
     where type world = ParserContext.world

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
     val reservedNames = ["Theorem", "Tactic", "Operator", "Print"])
  open TP

  fun parseTm fvs w =
    squares (Syntax.parseAbt (lookupOperator w) (Syntax.initialState fvs))

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

  fun parseOperatorDef w =
    parsePattern w -- (fn pat =>
      succeed pat && (symbol "=def=" >> parseTm (Syntax.freeVariables pat) w)
    ) wth (fn (P : Syntax.t, N : Syntax.t) =>
              (w, DevelopmentAst.DEFINITION (P, N)))

  val parseCommand =
    reserved "Print" >> parseLabel
      wth DevelopmentAst.COMMAND o DevelopmentAst.PRINT

  fun parseDecl w =
      parseTheorem w
      || parseTactic w
      || parseOperatorDecl w
      || parseOperatorDef w
      || parseCommand wth (fn r => (w,r))

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
   structure ParserContext = StringVariableContext)
