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
    val commentStart = SOME "(*"
    val commentEnd = SOME "*)"
    val commentLine = SOME "|||"
    val nestedComments = false

    val identLetter = CharParser.letter
    val identStart = identLetter
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = ["refine"]
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TP = TokenParser (LangDef)
  open TP

  val parse_id : (state -> tactic) charParser = symbol "id" return (fn _ => ID)
  fun parse_script () : (state -> tactic) charParser =
    separate1 ((squares (commaSep ($ parse_script)) wth Sum.INL) <|> ($ plain wth Sum.INR)) semi
    wth (foldl (fn (t1, t2) => fn s =>
                   case t1 of
                        Sum.INR t => THEN (t2 s, t s)
                      | Sum.INL x => THENL (t2 s, map (fn t' => t' s) x)) (fn _ => ID))

  and plain () = parse_rule || $ parse_try || $ parse_repeat || parse_id

  and parse_try () =
        middle (symbol "?{") ($ parse_script) (symbol "}")
          wth (fn t => TRY o t)

  and parse_repeat () =
        middle (symbol "*{") ($ parse_script) (symbol "}")
          wth (fn t => REPEAT o t)

  val parse = $ parse_script << opt (dot || semi)
end

