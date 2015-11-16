signature COQ =
sig
    type term
    structure Syntax : ABT_UTIL sharing type Syntax.t = term
    structure Sequent : SEQUENT sharing type Sequent.term = term

    val toCoq : Sequent.sequent -> term -> string
end
