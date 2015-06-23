signature PARSER_CONTEXT =
sig
    type world
    type label
    exception NoSuchOperator of label

    val new : (label * Arity.t) list -> world

    val lookupOperator : world -> label -> Arity.t
    val declareOperator : world -> (label * Arity.t) -> world

    (* This should only return operators added with
     * declareOperator, not things given to new
     *)
    val enumerateOperators : world -> (label * Arity.t) list
end
