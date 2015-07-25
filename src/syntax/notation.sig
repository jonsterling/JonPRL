signature NOTATION =
sig
  datatype t =
      INFIX of string * ParserCombinators.associativity * int
    | PREFIX of string * int
    | POSTFIX of string * int

  val toString : t -> string
  val parse : t CharParser.charParser
end
