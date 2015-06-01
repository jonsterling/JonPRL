functor DevelopmentParser
  (structure Syntax : PARSE_ABT
   structure Development : DEVELOPMENT
   structure Sequent : SEQUENT
   structure TacticScript : TACTIC_SCRIPT

   sharing Development.Telescope.Label = Syntax.Variable
   sharing TacticScript.Lcf = Development.Lcf
   sharing type Development.term = Syntax.t
   sharing type Sequent.term = Development.term
   sharing type TacticScript.state = Development.t
   sharing type TacticScript.Lcf.goal = Sequent.sequent
  ) : DEVELOPMENT_PARSER =
struct
  structure Development = Development

  open ParserCombinators CharParser
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

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
    val reservedNames = ["Theorem", "Tactic"]
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TP = TokenParser (LangDef)
  open TP

  val parse_tm =
    middle (symbol "[") Syntax.parse_abt (symbol "]")
      || middle (symbol "⌊") Syntax.parse_abt (symbol "⌋")

  val parse_name =
    identifier
      wth Syntax.Variable.named

  val parse_definition =
    parse_name << symbol "=def="
      && parse_tm
      wth (fn (definiendum, definiens) => fn D =>
             Development.define D (definiendum, definiens))

  val parse_theorem =
    reserved "Theorem" >> parse_name << symbol ":"
      && parse_tm
      && braces TacticScript.parse
      wth (fn (thm, (M, tac)) => fn D =>
             Development.prove D (thm, Sequent.>> (Sequent.Context.empty, M), tac D))

  val parse_tactic =
    reserved "Tactic" >> parse_name
      && braces TacticScript.parse
      wth (fn (lbl, tac) => fn D => Development.define_tactic D (lbl, tac D))

  fun parse dev =
    sepEnd (parse_definition || parse_theorem || parse_tactic) dot << not any
      wth (foldl (fn (K, D) => K D) dev)

end

structure CttDevelopmentParser = DevelopmentParser
  (structure Syntax = Syntax
   structure Development = Development
   structure Sequent = Sequent
   structure TacticScript = CttScript)
