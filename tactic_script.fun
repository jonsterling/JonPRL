functor TacticScript
  (structure Lcf : LCF
   type state
   val parse_rule : (state -> Lcf.tactic) CharParser.charParser) : TACTIC_SCRIPT =
struct
  structure Lcf = Lcf
  type state = state

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

  val parse_id : (state -> tactic) charParser = symbol "id" return (fn _ => ID)
  fun parse_script () : (state -> tactic) charParser =
    separate1 ($ plain) semi
    wth (foldr (fn (t1, t2) => fn s => THEN (t1 s, t2 s)) (fn _ => ID))

  and plain () = parse_rule || $ parse_try || $ parse_repeat || parse_id

  and parse_thenl () =
    $ parse_script << semi
      && squares (commaSep ($ parse_script))
      wth (fn (t, ts) => fn s => THENL (t s, map (fn t' => t' s) ts))

  and parse_try () =
        middle (symbol "?{") ($ parse_script) (symbol "}")
          wth (fn t => TRY o t)

  and parse_repeat () =
        middle (symbol "*{") ($ parse_script) (symbol "}")
          wth (fn t => REPEAT o t)

  val parse = (not any return (fn _ => ID)) || ($ parse_script << symbol ".")
end

