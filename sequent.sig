signature SEQUENT =
sig
  type term

  structure Context : CONTEXT
  type name = Context.name

  type context = term Context.context

  datatype sequent = >> of context * term
  val to_string : PrintMode.t -> sequent -> string
end

