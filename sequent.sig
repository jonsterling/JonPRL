signature SEQUENT =
sig
  type term
  type name

  structure Context : CONTEXT
    where type name = name

  type context = term Context.context

  datatype sequent = >> of context * term

  val to_string : PrintMode.t -> sequent -> string
end

