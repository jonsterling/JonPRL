signature UNIFY_SEQUENT =
sig
  structure Sequent : SEQUENT

  exception Mismatch

  type input =
       {hyps : Sequent.term list,
        goal : Sequent.term}
  type output =
       {matched : Sequent.name list,
        subst : (Sequent.Context.Syntax.Variable.t * Sequent.term) list}

  val unify : input * Sequent.sequent -> output
end
