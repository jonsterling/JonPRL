signature RESOURCE =
sig
  structure Variable : VARIABLE

  datatype t = AUTO | ELIM | EQ_CD | INTRO | CUSTOM of Variable.t

  val toString : t -> string
  val parse : (string -> t) -> t CharParser.charParser
end
