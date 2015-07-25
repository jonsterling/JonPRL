structure DevelopmentAst : DEVELOPMENT_AST =
struct
  type label = string

  structure Syntax = Syntax
  structure Tactic  = Tactic

  datatype command =
      PRINT of Syntax.Operator.t
    | EVAL of Syntax.t * int option

  datatype t =
      THEOREM of label * Syntax.t * Tactic.t
    | OPERATOR of label * Arity.t
    | TACTIC of label * Tactic.t
    | DEFINITION of Syntax.t * Syntax.t
    | NOTATION of Notation.t * Syntax.Operator.t
    | COMMAND of command
end
