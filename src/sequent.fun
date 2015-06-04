functor Sequent (structure Context : CONTEXT) : SEQUENT =
struct
  type term = Syntax.t

  structure Context = Context
  type name = Context.name
  type context = term Context.context
  datatype sequent = >> of context * term

  infix >>

  fun to_string (H >> P) =
    let
      val ctx = Context.to_string Syntax.to_string H
      val prop = Syntax.to_string P
    in
      ctx ^ "\n⊢ " ^ prop
    end

  fun eq (H >> P, H' >> P') =
    Context.eq Syntax.eq (H, H') andalso Syntax.eq (P, P')

end

structure Sequent = Sequent (structure Context = Context)
