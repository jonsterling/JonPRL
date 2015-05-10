signature EXTRACT =
sig
  type evidence
  type term

  val extract : evidence -> term
end
