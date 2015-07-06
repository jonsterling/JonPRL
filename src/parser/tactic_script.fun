functor TacticScript
  (structure Tactic : TACTIC
   structure RuleParser : INTENSIONAL_PARSER
     where type t = Tactic.t) : TACTIC_SCRIPT =
struct
  type world = RuleParser.world
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

  fun parseScript w () : tactic charParser =
    separate ((squares (commaSep ($ (parseScript w))) wth Sum.INR)
                   <|> ($ (plain w) wth Sum.INL)) semi
    wth THEN

  and plain w () =
    RuleParser.parse w
      || $ (parseTry w)
      || $ (parseRepeat w)
      || $ (parseOrelse w)
      || $ (parseComplete w)
      || parseId
      || parseFail
      || parseTrace

  and parseTry w () =
    middle (symbol "?{") ($ (parseScript w)) (symbol "}")
    wth TRY

  and parseRepeat w () =
    middle (symbol "*{") ($ (parseScript w)) (symbol "}")
    wth LIMIT

  and parseOrelse w () =
    !! (parens (separate1 ($ (parseScript w)) pipe))
    wth (fn (ts, pos) => ORELSE (ts, {name = "ORELSE", pos = pos}))

  and parseComplete w () =
    !! (middle (symbol "!{") ($ (parseScript w)) (symbol "}"))
    wth (fn (t, pos) => COMPLETE (t, {name = "COMPLETE", pos = pos}))

  fun parse w = $ (parseScript w) << opt (dot || semi)
end
