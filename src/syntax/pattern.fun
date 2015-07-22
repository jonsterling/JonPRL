structure PatternOperatorType =
struct
  datatype ('builtin, 'label) operator =
      CUSTOM of 'label * Arity.t
    | BUILTIN of 'builtin
end

functor PatternOperator
  (structure Label : PARSE_LABEL
   structure Builtin : PARSE_OPERATOR
    where type world = Label.t -> Arity.t) : PARSE_OPERATOR =
struct
  open Builtin
  fun arity oper =
    Vector.map (fn _ => 0) (Builtin.arity oper)
end

structure PatternSyntax : PARSE_ABT =
struct
  structure PatternOperator = PatternOperator
    (structure Label = ParseLabel (StringVariable)
     structure Builtin = Syntax.ParseOperator)
  structure Abt = Abt
    (structure Operator = PatternOperator
     structure Variable = Syntax.Variable)
  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = PatternOperator)

  open ParseAbt
end


