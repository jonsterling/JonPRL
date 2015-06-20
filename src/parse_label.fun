functor ParseLabel (L : LABEL where type t = string) : PARSE_LABEL =
struct
  open L ParserCombinators infix wth
  val parseLabel = JonprlTokenParser.identifier
end
