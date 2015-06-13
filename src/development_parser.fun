functor DevelopmentParser
  (structure Development : DEVELOPMENT where type Telescope.Label.t = string
   structure Syntax : PARSE_ABT
    where type Operator.t = Development.Telescope.Label.t OperatorType.operator
    where type ParseOperator.env = Development.Telescope.Label.t -> Arity.t
   structure Sequent : SEQUENT
   structure TacticScript : TACTIC_SCRIPT

   sharing TacticScript.Lcf = Development.Lcf
   sharing type Development.term = Syntax.t
   sharing type Sequent.term = Development.term
   sharing type TacticScript.env = Development.t
   sharing type TacticScript.Lcf.goal = Sequent.sequent
  ) : DEVELOPMENT_PARSER =
struct
  structure Development = Development

  open ParserCombinators CharParser
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >> --

  structure LangDef :> LANGUAGE_DEF =
  struct
    type scanner = char CharParser.charParser
    val commentStart = SOME "(*"
    val commentEnd = SOME "*)"
    val commentLine = SOME "|||"
    val nestedComments = false

    val identLetter = CharParser.letter || CharParser.oneOf (String.explode "-'_ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσΤτΥυΦφΧχΨψΩω") || CharParser.digit
    val identStart = identLetter
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = ["Theorem", "Tactic", "Operator"]
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TP = TokenParser (LangDef)
  open TP

  val lookupOperator = Development.lookupOperator

  fun parseTm fvs = squares o Syntax.parseAbt fvs o lookupOperator

  val parseName =
    identifier
      wth Syntax.Variable.named

  fun parseTheorem D =
    reserved "Theorem" >> identifier << colon
      && parseTm [] D
      && braces (TacticScript.parse D)
      wth (fn (thm, (M, tac)) =>
             Development.prove D
              (thm, Sequent.>> (Sequent.Context.empty, M), tac))

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parseArity =
    parens (semiSep parseInt)
    wth Vector.fromList

  fun parseTactic D =
    reserved "Tactic" >> identifier
      && braces (TacticScript.parse D)
      wth (fn (lbl, tac) => Development.defineTactic D (lbl, tac))

  fun parseOperatorDecl D =
    (reserved "Operator" >> identifier << colon && parseArity)
    wth Development.declareOperator D

  fun parseOperatorDef D =
    parseTm [] D -- (fn (tm : Syntax.t) =>
      succeed tm && (symbol "=def=" >> parseTm (Syntax.freeVariables tm) D)
    ) wth (fn (M : Syntax.t, N : Syntax.t) =>
      Development.defineOperator D
        {definiendum = M,
         definiens = N})

  fun parseDecl D =
      parseTheorem D
      || parseTactic D
      || parseOperatorDecl D
      || parseOperatorDef D

  fun parse' D () =
    (parseDecl D << dot) -- (fn D' =>
      $ (parse' D') <|>
      (whiteSpace >> not any) return D')

  fun parse D = ($ (parse' D))
end

structure CttDevelopmentParser = DevelopmentParser
  (structure Syntax = Syntax
   structure Development = Development
   structure Sequent = Sequent
   structure TacticScript = CttScript)
