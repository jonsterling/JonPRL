structure ParserContext :> PARSER_CONTEXT =
struct
  type label = Label.t

  structure Dict = SplayDict(structure Key = Label)
  structure NotationDict = SplayDict(structure Key = StringVariable)

  type world =
    {initial : (Arity.t * Notation.t option) Dict.dict,
     added : (Arity.t * Notation.t option) Dict.dict,
     notations : label NotationDict.dict}

  exception NoSuchOperator of label

  fun new bnds =
    {initial =
       List.foldl
         (fn ((lbl, a, n), wld) => Dict.insert wld lbl (a, n))
         Dict.empty
         bnds,
     added = Dict.empty,
     notations =
       List.foldl
         (fn ((lbl, a, SOME n), wld) => NotationDict.insert wld (Notation.symbol n) lbl
           | (_, wld) => wld)
         NotationDict.empty
         bnds}

  fun lookupOperator {initial, added, notations} lbl =
    case Dict.find added lbl of
        NONE => (Dict.lookup initial lbl handle _ => raise NoSuchOperator lbl)
      | SOME a => a

  fun declareOperator {initial, added, notations} (lbl, arity) =
    {initial = initial,
     added = Dict.insert added lbl (arity, NONE),
     notations = notations}

  fun declareNotation {initial, added, notations} (lbl, notation) =
    {initial = initial,
     added =
       case Dict.lookup added lbl of
            (arity, NONE) => Dict.insert added lbl (arity, SOME notation)
          | _ => raise Subscript,
     notations = NotationDict.insert notations (Notation.symbol notation) lbl
    }

  fun lookupNotation {initial, added, notations} =
    NotationDict.lookup notations

  fun enumerateOperators {initial, added, notations} =
    Dict.toList added
end
