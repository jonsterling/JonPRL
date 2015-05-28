functor Sequent
  (structure Syntax : ABT_UTIL
   structure Context : CONTEXT) : SEQUENT =
struct
  type term = Syntax.t

  structure Context = Context
  type name = Context.Name.t

  type context = term Context.context
  datatype sequent = >> of context * term

  infix >>

  fun to_string print_mode (G >> P) =
    let
      val ctx = Context.to_string (print_mode, Syntax.to_string) G
      val prop = Syntax.to_string print_mode P
    in
      ctx ^ " ⊢ " ^ prop
    end
end

