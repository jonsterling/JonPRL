functor Sequent (structure Context : CONTEXT) : SEQUENT =
struct
  type term = Syntax.t

  structure Context = Context
  type name = Context.name

  type context = term Context.context
  datatype sequent = >> of context * term

  infix >>

  fun to_string (G >> P) =
    let
      val ctx = Context.to_string Syntax.to_string G
      val prop = Syntax.to_string P
    in
      ctx ^ " ⊢ " ^ prop
    end
end

structure Sequent = Sequent (structure Context = Context)
