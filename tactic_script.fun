functor TacticScript
  (structure Lcf : LCF
   val parse_rule : Lcf.tactic CharParser.charParser) : TACTIC_SCRIPT =
struct
  structure Lcf = Lcf

  structure Tacticals = Tacticals (Lcf)
  open Lcf Tacticals ParserCombinators CharParser
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  structure LangDef :> LANGUAGE_DEF =
  struct
    type scanner = char CharParser.charParser
    val commentStart = NONE
    val commentEnd = NONE
    val commentLine = NONE
    val nestedComments = false

    val identLetter = CharParser.letter
    val identStart = identLetter
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = []
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TP = TokenParser (LangDef)
  open TP

  fun parse_script () = separate1 ($ plain) semi wth foldr THEN ID

  and plain () = parse_rule || $ parse_try || $ parse_repeat || $ parse_thenl

  and parse_thenl () =
    $ parse_script << semi
      && squares (commaSep ($ parse_script))
      wth THENL

  and parse_try () =
        middle (symbol "?{") ($ parse_script) (symbol "}")
          wth TRY

  and parse_repeat () =
        middle (symbol "*{") ($ parse_script) (symbol "}")
          wth REPEAT

  val parse = (not any return ID) || ($ parse_script << symbol ".")

end

