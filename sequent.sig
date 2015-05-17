signature SEQUENT =
sig
  type term

  structure Name : VARIABLE
  structure Context : CONTEXT where Name = Name
  type name = Name.t

  type context = term Context.context

  datatype sequent = >> of context * term

  val to_string : PrintMode.t -> sequent -> string
end

