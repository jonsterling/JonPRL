functor Sequent
  (structure Syntax : ABTUTIL
   structure Context : CONTEXT
     where type name = Syntax.Variable.t) : SEQUENT =
struct
  type term = Syntax.t
  type name = Syntax.Variable.t

  structure Context = Context

  type context = term Context.context
  datatype sequent = >> of context * term

  infix >>

  fun to_string print_mode (G >> P) =
    let
      val ctx = Context.to_string (print_mode, Syntax.to_string) G
      val prop = Syntax.to_string print_mode P
    in
      ctx ^ " ≫ " ^ prop
    end
end

