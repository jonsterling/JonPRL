functor ParserContext(structure Ord : ORDERED) :>
        PARSER_CONTEXT where type label = Ord.t =
struct
  type label = Ord.t

  structure Dict = SplayDict(structure Key = Ord)
  type world = Arity.t Dict.dict

  exception NoSuchOperator of label

  val empty = Dict.empty

  fun lookupOperator dict lbl =
    case Dict.find dict lbl of
        NONE => raise NoSuchOperator lbl
      | SOME a => a

  fun declareOperator dict (lbl, arity) = Dict.insert dict lbl arity

  fun enumerateOperators dict = Dict.toList dict
end

structure StringVariableContext = ParserContext(structure Ord = StringVariable)
