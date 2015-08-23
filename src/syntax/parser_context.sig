signature PARSER_CONTEXT =
sig
  type world
  type label = Label.t
  type operator = UniversalOperator.t
  exception NoSuchOperator of label
  exception NoSuchResource of string

  val new : (label * operator * Notation.t option) list -> world

  val lookupOperator : world -> label -> operator * Notation.t option
  val declareOperator : world -> label * Arity.t -> world
  val declareNotation : world -> operator * Notation.t -> world
  val lookupNotation : world -> string -> label

  val lookupResource : world -> string -> Resource.t
  val declareResource : world -> string -> world

  (* This should only return operators added with
   * declareOperator, not things given to new
   *)
  val enumerateOperators : world -> (label * (operator * Notation.t option)) list
end
