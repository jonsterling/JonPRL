functor TacticScript
  (structure Tactic : TACTIC
   structure RuleParser : INTENSIONAL_PARSER
     where type t = Tactic.t
     where type world = ParserContext.world
   structure ParseSyntax : PARSE_ABT
     where type t = Tactic.term
     where type Variable.t = Tactic.name
     where type ParseOperator.world = ParserContext.world)
        : TACTIC_SCRIPT =
struct
  type world = ParserContext.world
  type tactic = Tactic.t

  open Tactic ParserCombinators CharParser ParserContext
  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  open JonprlTokenParser

  val pipe = symbol "|"

  val name = identifier wth ParseSyntax.Variable.named

  fun parseTm w =
    ParseSyntax.parseAbt w (ParseSyntax.initialState [])

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

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
    sepEnd' ((squares (commaSep ($ (parseScript w))) wth LIST)
                 || ($ (parseFocus w) wth FOCUS)
                 || ($ (plain w) wth APPLY)) semi
    wth THEN

  and plain w () =
    $ (parseTry w)
      || $ (parseRepeat w)
      || $ (parseProgress w)
      || $ (parseOrelse w)
      || $ (parseComplete w)
      || $ (parsePrune w)
      || parseId
      || parseFail
      || parseTrace
      || $ (parseMatch w)
      || $ (parseOnAux w)
      || $ (parseOnMain w)
      || RuleParser.parse w

  and parseOnAux w () =
    symbol "aux" >>
    whiteSpace >> middle (symbol "{") ($ (parseScript w)) (symbol "}")
    wth (fn t => ON_CLASS (Goal.AUX, t))

  and parseOnMain w () =
    symbol "main" >>
    whiteSpace >> middle (symbol "{") ($ (parseScript w)) (symbol "}")
    wth (fn t => ON_CLASS (Goal.MAIN, t))

  and parseFocus w () =
    symbol "focus" && parseInt &&
    whiteSpace >> middle (symbol "#{") ($ (parseScript w)) (symbol "}")
    wth (fn (_, (i, t)) => (i, t))

  and parsePrune w () =
    symbol "prune" >>
    whiteSpace >> middle (symbol "{") ($ (parseScript w)) (symbol "}")
    wth PRUNE

  and parseTry w () =
    middle (symbol "?{") ($ (parseScript w)) (symbol "}")
    wth TRY

  and parseRepeat w () =
    middle (symbol "*{") ($ (parseScript w)) (symbol "}")
    wth LIMIT

  and parseProgress w () =
    symbol "progress" >>
    whiteSpace >> middle (symbol "{") ($ (parseScript w)) (symbol "}")
    wth PROGRESS

  and parseMatch w () =
    let
      val hyp = name && symbol ":" && parseTm w wth (fn (n, (_, h)) => (n, h))
      val parsePattern =
        squares (commaSep hyp && symbol "|-" && parseTm w)
        wth (fn (hyps, (_, goal)) => CtxPattern {goal = goal, hyps = hyps})
    in
      middle (symbol "@{")
             (separate1 (parsePattern && symbol "=>" && ($ (parseScript w))) pipe)
             (symbol "}")
      wth (MATCH o List.map (fn (pat, (_, body)) => (pat, branch body)))
    end

  and parseOrelse w () =
    !! (parens (separate1 ($ (parseScript w)) pipe))
    wth (fn (ts, pos) => ORELSE (ts, {name = "ORELSE", pos = pos}))

  and parseComplete w () =
    !! (middle (symbol "!{") ($ (parseScript w)) (symbol "}"))
    wth (fn (t, pos) => COMPLETE (t, {name = "COMPLETE", pos = pos}))

  fun parse w = $ (parseScript w) << opt dot
end
