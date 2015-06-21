functor TacticScript
  (structure Tactic : TACTIC
   type world
   val parseRule : world -> Tactic.t CharParser.charParser)
        : TACTIC_SCRIPT =
struct
  type world = world
  type tactic = Tactic.t

  open Tactic ParserCombinators CharParser
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  structure TP = TokenParser
    (open JonprlLanguageDef
     val reservedNames = ["refine"])
  open TP

  val pipe = symbol "|"

  val parseId : tactic charParser =
    !! (symbol "id") wth (fn (name, pos) =>
      ID {name = name, pos = pos})

  val parseFail : tactic charParser =
    !! (symbol "fail") wth (fn (name, pos) =>
      FAIL {name = name, pos = pos})

  val parseTrace : tactic charParser =
    !! (symbol "trace") && stringLiteral
      wth (fn ((name, pos), msg) =>
              TRACE (msg, {name = name, pos = pos}))

  fun parseScript D () : tactic charParser =
    separate1 ((squares (commaSep ($ (parseScript D))) wth Sum.INR)
                   <|> ($ (plain D) wth Sum.INL)) semi
    wth THEN

  and plain D () =
    parseRule D
      || $ (parseTry D)
      || $ (parseRepeat D)
      || $ (parseOrelse D)
      || parseId
      || parseFail
      || parseTrace

  and parseTry D () =
        middle (symbol "?{") ($ (parseScript D)) (symbol "}")
          wth TRY

  and parseRepeat D () =
        middle (symbol "*{") ($ (parseScript D)) (symbol "}")
        wth REPEAT

  and parseOrelse D () =
        parens (separate1 ($ (parseScript D)) pipe)
        wth ORELSE

  fun parse D = $ (parseScript D) << opt (dot || semi)
end
