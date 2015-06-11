functor TacticScript
  (structure Lcf : ANNOTATED_LCF where type metadata = TacticMetadata.metadata
   structure LcfApart : LCF_APART
     where type goal = Lcf.goal
     where type evidence = Lcf.evidence

   type env
   val parse_rule : env -> Lcf.tactic CharParser.charParser) : TACTIC_SCRIPT =
struct
  structure Lcf = Lcf
  type env = env

  structure Tacticals = ProgressTacticals (LcfApart)
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

  fun parse_script D () : tactic charParser =
    separate1 ((squares (commaSep ($ (parse_script D))) wth Sum.INL) <|> ($ (plain D) wth Sum.INR)) semi
    wth (foldl (fn (t1, t2) =>
                   case t1 of
                        Sum.INR t => THEN (t2, t)
                      | Sum.INL ts => THENL (t2, ts)) ID)

  and plain D () =
    parse_rule D
      || $ (parse_try D)
      || $ (parse_repeat D)
      || $ (parse_orelse D)
      || parse_id
      || parse_fail

  and parse_try D () =
        middle (symbol "?{") ($ (parse_script D)) (symbol "}")
          wth TRY

  and parse_repeat D () =
        middle (symbol "*{") ($ (parse_script D)) (symbol "}")
          wth LIMIT

  and parse_orelse D () =
        parens (separate1 ($ (parse_script D)) pipe)
        wth foldl ORELSE FAIL

  fun parse D = $ (parse_script D) << opt (dot || semi)
end

