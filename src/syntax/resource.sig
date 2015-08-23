signature RESOURCE =
sig
  datatype t = AUTO | ELIM | EQ_CD | INTRO | WF

  val toString : t -> string
  val parse : t CharParser.charParser
end
