signature ABT =
sig
  structure Variable : VARIABLE
  structure Operator : OPERATOR

  type t

  datatype 'a view
    = ` of Variable.t
    | \ of Variable.t * 'a
    | $ of Operator.t * 'a vector

  exception Malformed of string

  val into : t view -> t
  val out : t -> t view

  val eq : t * t -> bool
  val map : ('a -> 'b) -> 'a view -> 'b view

end
