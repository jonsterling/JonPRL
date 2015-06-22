signature PARSER_CONTEXT =
sig
    type world
    type label
    exception NoSuchOperator of label

    val empty : world
    val lookupOperator : world -> label -> Arity.t
    val declareOperator : world -> (label * Arity.t) -> world

    val enumerateOperators : world -> (label * Arity.t) list
end
