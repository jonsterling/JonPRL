signature PARSE_ABT =
sig
  include ABT_UTIL

  type state
  val parse_abt : (state -> t) CharParser.charParser
end

