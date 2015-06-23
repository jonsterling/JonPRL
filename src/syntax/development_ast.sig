signature DEVELOPMENT_AST =
sig
  type label

  structure Syntax : ABT
    where type Operator.t = label OperatorType.operator

  structure Pattern : ABT

  structure Tactic : TACTIC
    where type label = label
    where type term = Syntax.t

  datatype t =
      THEOREM of label * Syntax.t * Tactic.t
    | OPERATOR of label * Arity.t
    | TACTIC of label * Tactic.t
    | DEFINITION of Pattern.t * Syntax.t
end
