signature PARSER_CONTEXT =
sig
    type world
    type label
    exception NoSuchOperator of label

    val lookupOperator : world -> label -> Arity.t
    val declareOperator : world -> (label * Arity.t) -> world
end
