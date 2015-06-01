signature SEQUENT =
sig
  type term
  type name
  type context

  datatype sequent = >> of context * term

  val eq : sequent * sequent -> bool
  val to_string : sequent -> string
end

