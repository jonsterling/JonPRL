functor TacticScript
  (structure Lcf : ANNOTATED_LCF where type metadata = TacticMetadata.metadata
   structure LcfApart : LCF_APART
     where type goal = Lcf.goal
     where type evidence = Lcf.evidence

   type env
   val parseRule : env -> Lcf.tactic CharParser.charParser) : TACTIC_SCRIPT =
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

  val parseId : tactic charParser =
    !! (symbol "id") wth (fn (name, pos) =>
      Lcf.annotate ({name = name, pos = pos}, ID))

  val parseFail : tactic charParser =
    !! (symbol "fail") wth (fn (name, pos) =>
      Lcf.annotate ({name = name, pos = pos}, FAIL))

  fun parseScript D () : tactic charParser =
    separate1 ((squares (commaSep ($ (parseScript D))) wth Sum.INL) <|> ($ (plain D) wth Sum.INR)) semi
    wth (foldl (fn (t1, t2) =>
                   case t1 of
                        Sum.INR t => THEN (t2, t)
                      | Sum.INL ts => THENL (t2, ts)) ID)

  and plain D () =
    parseRule D
      || $ (parseTry D)
      || $ (parseRepeat D)
      || $ (parseOrelse D)
      || parseId
      || parseFail

  and parseTry D () =
        middle (symbol "?{") ($ (parseScript D)) (symbol "}")
          wth TRY

  and parseRepeat D () =
        middle (symbol "*{") ($ (parseScript D)) (symbol "}")
          wth LIMIT

  and parseOrelse D () =
        parens (separate1 ($ (parseScript D)) pipe)
        wth foldl ORELSE FAIL

  fun parse D = $ (parseScript D) << opt (dot || semi)
end

