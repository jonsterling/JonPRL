structure DevelopmentAst : DEVELOPMENT_AST =
struct
  type label = string

  structure Syntax = Syntax
  structure Pattern = PatternSyntax
  structure Tactic  = Tactic

  datatype t
    = THEOREM of label * Syntax.t * Tactic.t
    | OPERATOR of label * Arity.t
    | TACTIC of label * Tactic.t
    | DEFINITION of Pattern.t * Syntax.t
end
