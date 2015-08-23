signature RESOURCE =
sig
  datatype t = AUTO | ELIM | EQ_CD | INTRO | CUSTOM of StringVariable.t

  val toString : t -> string
  val parse : t CharParser.charParser
end
