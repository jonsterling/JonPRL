signature INTENSIONAL_PARSER =
sig
  type t
  type world
  val parse : world -> t CharParser.charParser
end
