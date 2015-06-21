signature PARSE_CTT =
  PARSE_ABT
    where type Operator.t = string OperatorType.operator
    where type ParseOperator.world = string -> Arity.t

signature PARSE_PATTERN =
  PARSE_ABT
    where type Operator.t = string PatternOperatorType.operator
    where type ParseOperator.world = string -> Arity.t

functor DevelopmentParser
  (structure Syntax : PARSE_CTT
   structure Pattern : PARSE_PATTERN
     where type Variable.t = Syntax.Variable.t

   structure Sequent : SEQUENT
     where type term = Syntax.t

   structure Development : DEVELOPMENT
     where type Telescope.Label.t = string
     where type judgement = Sequent.sequent
     where type pattern = Pattern.t
     where type term = Syntax.t

   structure DevelopmentAst : DEVELOPMENT_AST
     where type label = Development.label
     where Syntax = Syntax
     where Pattern = Pattern
     where Tactic = Tactic

   structure TacticScript : TACTIC_SCRIPT
     where type tactic = Tactic.t
     where type world  = Development.world) : DEVELOPMENT_PARSER =
struct
  structure Development = Development
  structure DevelopmentAst = DevelopmentAst

  open ParserCombinators CharParser
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >> --

  structure TP = TokenParser
    (open JonprlLanguageDef
     val reservedNames = ["Theorem", "Tactic", "Operator"])
  open TP

  val lookupOperator = Development.lookupOperator

  fun parseTm fvs = squares o Syntax.parseAbt fvs o lookupOperator
  val parsePattern = squares o Pattern.parseAbt [] o lookupOperator

  val parseName =
    identifier
      wth Syntax.Variable.named

  fun parseTheorem D =
    reserved "Theorem" >> identifier << colon
      && parseTm [] D
      && braces (TacticScript.parse D)
      wth (fn (thm, (M, tac)) =>
             (D, DevelopmentAst.THEOREM (thm, M, tac)))

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parseArity =
    parens (semiSep parseInt)
    wth Vector.fromList

  fun parseTactic D =
    reserved "Tactic" >> identifier
      && braces (TacticScript.parse D)
      wth (fn (lbl, tac) =>
              (D, DevelopmentAst.TACTIC (lbl, tac)))

  fun parseOperatorDecl D =
    (reserved "Operator" >> identifier << colon && parseArity)
     wth (fn (lbl, arity) =>
             (Development.declareOperator D (lbl, arity),
              DevelopmentAst.OPERATOR (lbl, arity)))

  fun parseOperatorDef D =
    parsePattern D -- (fn (pat : Pattern.t) =>
      succeed pat && (symbol "=def=" >> parseTm (Pattern.freeVariables pat) D)
    ) wth (fn (P : Pattern.t, N : Syntax.t) =>
              (D, DevelopmentAst.DEFINITION (P, N)))

  fun parseDecl D =
      parseTheorem D
      || parseTactic D
      || parseOperatorDecl D
      || parseOperatorDef D

  fun parse' D ast () =
    whiteSpace >>
    (parseDecl D << dot) -- (fn (D', decl) =>
      $ (parse' D' (decl :: ast)) <|>
      (whiteSpace >> not any) return (D', ast))

  fun parse D = ($ (fn () => parse' D [] ()
                             wth (fn (D, ast) => (D, List.rev ast))))
end

structure CttDevelopmentParser = DevelopmentParser
  (structure Syntax = Syntax
   structure Pattern = PatternSyntax
   structure Development = Development
   structure DevelopmentAst = DevelopmentAst
   structure Sequent = Sequent
   structure TacticScript = CttScript)
