signature COQ =
sig
  structure Syntax : ABT_UTIL
    where type Operator.t = UniversalOperator.t
  structure Sequent : SEQUENT
    where type term = Syntax.t
    where Context.Syntax = Syntax

  exception TODO of string
  exception Malformed of string

  val toCoq : Sequent.sequent -> Syntax.t -> (string * string) (* statement/proof *)
end
