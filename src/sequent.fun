functor Sequent (structure Context : CONTEXT) : SEQUENT =
struct
  type term = Syntax.t

  structure Context = Context
  type name = Context.name
  type context = Context.context
  datatype sequent = >> of context * term

  infix >>

  fun toString (H >> P) =
    let
      val ctx = Context.toString H
      val prop = Syntax.toString P
    in
      if Context.isEmpty H then
        "⊢ " ^ prop
      else
        Context.toString H ^ "\n⊢ " ^ prop
    end

  fun eq (H >> P, H' >> P') =
    Context.eq (H, H') andalso Syntax.eq (P, P')

end

structure Sequent = Sequent (structure Context = Context)
