structure ParserContext :> PARSER_CONTEXT =
struct
  type label = Label.t
  type operator = UniversalOperator.t

  structure Dict = SplayDict(structure Key = Label)

  (* to look up the fixity of a notational symbol *)
  structure NotationDict = SplayDict(structure Key = StringVariable)
  structure ResourceDict = SplayDict(structure Key =
                                     struct
                                       type t = string
                                       val eq = op=
                                       open String
                                     end)

  type world =
    {initial : (operator * Notation.t option) Dict.dict,
     added : (operator * Notation.t option) Dict.dict,
     notations : label NotationDict.dict,
     resources : Resource.t ResourceDict.dict}

  exception NoSuchOperator of label
  exception NoSuchResource of string

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
         bnds,
     resources = ResourceDict.empty}

  fun lookupOperator {initial, added, notations, resources} lbl =
    case Dict.find added lbl of
        NONE => (Dict.lookup initial lbl handle _ => raise NoSuchOperator lbl)
      | SOME a => a

  fun declareOperator {initial, added, notations, resources} (lbl, arity) =
    let
      datatype theta = THETA
      val {inject, project} =
        OperatorUniverse.embed
          ((), {arity = fn THETA => arity,
                toString = fn THETA => lbl,
                eq = fn (THETA, THETA) => true})
    in
      {initial = initial,
       added = Dict.insert added lbl (inject THETA, NONE),
       notations = notations,
       resources = resources}
    end

  fun declareNotation {initial, added, notations, resources} (theta, notation) =
    let
      val lbl = UniversalOperator.toString theta
    in
      {initial = initial,
       added = Dict.insert added lbl (theta, SOME notation),
       notations = NotationDict.insert notations (Notation.symbol notation) lbl,
      resources = resources}
    end

  fun lookupNotation {initial, added, notations, resources} =
    NotationDict.lookup notations

  fun declareResource {initial, added, notations, resources} s =
      {initial = initial,
       added = added,
       notations = notations,
       resources = ResourceDict.insert resources s
                                       (Resource.CUSTOM (Resource.Variable.named s))}

  fun lookupResource {initial, added, notations, resources} s =
    ResourceDict.lookup resources s handle ResourceDict.Absent =>
      raise NoSuchResource s

  fun enumerateOperators {initial, added, notations, resources} =
    Dict.toList added
end
