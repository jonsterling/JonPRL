functor PatternOperator (Operator : PARSE_OPERATOR) : PARSE_OPERATOR =
struct
  open Operator
  fun arity oper =
    Vector.map (fn _ => 0) (Operator.arity oper)
end

structure PatternSyntax : PARSE_ABT =
struct
  structure PatternOperator = PatternOperator (Syntax.ParseOperator)
  structure Abt = Abt
    (structure Operator = PatternOperator
     structure Variable = Syntax.Variable)
  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = PatternOperator)

  open ParseAbt
end


