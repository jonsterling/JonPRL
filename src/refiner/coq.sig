signature COQ =
sig
  structure Syntax : ABT_UTIL
    where type Operator.t = UniversalOperator.t
  structure Sequent : SEQUENT
    where type term = Syntax.t
    where Context.Syntax = Syntax

  val toCoq : Sequent.sequent -> Syntax.t -> string
end
