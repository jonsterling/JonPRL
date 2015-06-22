signature PARSE_CTT =
  PARSE_ABT
    where type Operator.t = string OperatorType.operator
    where type ParseOperator.world = string -> Arity.t

signature PARSE_PATTERN =
  PARSE_ABT
    where type Operator.t = string PatternOperatorType.operator
    where type ParseOperator.world = string -> Arity.t

functor DevelopmentParser
  (structure Tactic : TACTIC
   structure Syntax : PARSE_ABT
     where type ParseOperator.world = Tactic.label -> Arity.t
   structure Pattern : PARSE_ABT
     where type Variable.t = Syntax.Variable.t
     where type ParseOperator.world = Tactic.label -> Arity.t
   structure Sequent : SEQUENT
     where type term = Syntax.t

   type world

   structure DevelopmentAst : DEVELOPMENT_AST
     where type Syntax.t = Syntax.t
     where type Pattern.t = Pattern.t
     where type Tactic.t = Tactic.t
     where type label    = Tactic.label

   structure TacticScript : TACTIC_SCRIPT
     where type tactic = Tactic.t
     where type world = world

   val declareOperator : TacticScript.world
                          -> (Tactic.label * Arity.t)
                          -> TacticScript.world
   val lookupOperator : TacticScript.world -> Tactic.label -> Arity.t

   val stringToLabel  : string -> Tactic.label) : DEVELOPMENT_PARSER =
struct
  type world = TacticScript.world
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

  fun parseTm fvs = squares o Syntax.parseAbt fvs o lookupOperator
  val parsePattern = squares o Pattern.parseAbt [] o lookupOperator

  val parseName =
    identifier
      wth Syntax.Variable.named

  val parseLabel = identifier wth stringToLabel

  fun parseTheorem D =
    reserved "Theorem" >> parseLabel << colon
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
    reserved "Tactic" >> parseLabel
      && braces (TacticScript.parse D)
      wth (fn (lbl, tac) =>
              (D, DevelopmentAst.TACTIC (lbl, tac)))

  fun parseOperatorDecl D =
    (reserved "Operator" >> parseLabel << colon && parseArity)
     wth (fn (lbl, arity) =>
             (declareOperator D (lbl, arity),
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
      (whiteSpace >> not any) return (D', decl :: ast))

  fun parse D = ($ (fn () => parse' D [] ()
                             wth (fn (D, ast) => (D, List.rev ast))))
end

structure CttDevelopmentParser = DevelopmentParser
  (structure Syntax = Syntax
   structure Tactic = Tactic
   structure Pattern = PatternSyntax
   structure DevelopmentAst = DevelopmentAst
   structure Sequent = Sequent
   structure TacticScript = CttScript
   val stringToLabel = StringVariable.named
   open StringVariableContext)
