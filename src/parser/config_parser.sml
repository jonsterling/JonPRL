structure ConfigParser :
  sig
    val parse : (string list) CharParser.charParser
  end =
struct
  open ParserCombinators CharParser

  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  val filename = repeat1 (not space >> anyChar) wth String.implode
  val parse = spaces >> separate1 filename spaces << spaces << eos
end
