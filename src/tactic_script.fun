functor TacticScript
  (structure Lcf : ANNOTATED_LCF where type metadata = TacticMetadata.metadata
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

  val pipe = symbol "|"

  val parse_id : tactic charParser =
    !! (symbol "id") wth (fn (name, pos) =>
      Lcf.annotate ({name = name, pos = pos}, ID))

  val parse_fail : tactic charParser =
    !! (symbol "fail") wth (fn (name, pos) =>
      Lcf.annotate ({name = name, pos = pos}, FAIL))

  fun parse_script () : (state -> tactic) charParser =
    separate1 ((squares (commaSep ($ parse_script)) wth Sum.INL) <|> ($ plain wth Sum.INR)) semi
    wth (foldl (fn (t1, t2) => fn s =>
                   case t1 of
                        Sum.INR t => THEN (t2 s, t s)
                      | Sum.INL x => THENL (t2 s, map (fn t' => t' s) x)) (fn _ => ID))

  and plain () =
    parse_rule
      || $ parse_try
      || $ parse_repeat
      || $ parse_orelse
      || parse_id wth (fn tac => fn _ => tac)
      || parse_fail wth (fn tac => fn _ => tac)

  and parse_try () =
        middle (symbol "?{") ($ parse_script) (symbol "}")
          wth (fn t => TRY o t)

  and parse_repeat () =
        middle (symbol "*{") ($ parse_script) (symbol "}")
          wth (fn t => REPEAT o t)

  and parse_orelse () =
        parens (separate1 ($ parse_script) pipe)
        wth foldl (fn (t1, t2) => fn s => ORELSE (t1 s, t2 s)) (fn _ => FAIL)

  val parse = $ parse_script << opt (dot || semi)
end

