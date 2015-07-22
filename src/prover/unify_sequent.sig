signature UNIFY_SEQUENT =
sig
  structure Sequent : SEQUENT

  exception Mismatch

  type input =
       {hyps : term list,
        goal : term}
  type output =
       {matched : name list,
        subst : (Context.Syntax.Variable.t * term) list}

  val unify : input * Sequent.sequent -> output
end
