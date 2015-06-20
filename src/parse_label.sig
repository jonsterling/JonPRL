signature PARSE_LABEL =
sig
  include LABEL
  val parseLabel : t CharParser.charParser
end

