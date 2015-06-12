functor DevelopmentParser
  (structure Development : DEVELOPMENT where type Telescope.Label.t = string
   structure Syntax : PARSE_ABT
    where type Operator.t = Development.Telescope.Label.t OperatorType.operator
    where type ParseOperator.env = Development.Telescope.Label.t -> int vector
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

  val lookup_operator = Development.lookup_operator

  fun parse_tm fvs = squares o Syntax.parse_abt fvs o lookup_operator

  val parse_name =
    identifier
      wth Syntax.Variable.named

  fun parse_theorem D =
    reserved "Theorem" >> identifier << colon
      && parse_tm [] D
      && braces (TacticScript.parse D)
      wth (fn (thm, (M, tac)) =>
             Development.prove D
              (thm, Sequent.>> (Sequent.Context.empty, M), tac))

  val parse_int =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parse_arity =
    parens (semiSep parse_int)
    wth Vector.fromList

  fun parse_tactic D =
    reserved "Tactic" >> identifier
      && braces (TacticScript.parse D)
      wth (fn (lbl, tac) => Development.define_tactic D (lbl, tac))

  fun parse_operator_decl D =
    (reserved "Operator" >> identifier << colon && parse_arity)
    wth Development.declare_operator D

  fun parse_operator_def D =
    parse_tm [] D -- (fn (tm : Syntax.t) =>
      succeed tm && (symbol "=def=" >> parse_tm (Syntax.free_variables tm) D)
    ) wth (fn (M : Syntax.t, N : Syntax.t) =>
      Development.define_operator D
        {definiendum = M,
         definiens = N})

  fun parse_decl D =
      parse_theorem D
      || parse_tactic D
      || parse_operator_decl D
      || parse_operator_def D

  fun parse' D () =
    (parse_decl D << dot) -- (fn D' =>
      $ (parse' D') <|>
      (whiteSpace >> not any) return D')

  fun parse D = ($ (parse' D))
end

structure CttDevelopmentParser = DevelopmentParser
  (structure Syntax = Syntax
   structure Development = Development
   structure Sequent = Sequent
   structure TacticScript = CttScript)
