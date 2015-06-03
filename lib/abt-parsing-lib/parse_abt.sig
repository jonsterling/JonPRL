signature PARSE_ABT =
sig
  include ABT_UTIL

  val parse_abt : t CharParser.charParser
end

