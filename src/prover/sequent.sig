signature SEQUENT =
sig
  type term

  structure Context : CONTEXT
  type name = Context.name
  type context = Context.context

  datatype sequent = >> of context * term

  val eq : sequent * sequent -> bool
  val toString : sequent -> string
end

