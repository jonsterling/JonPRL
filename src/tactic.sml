structure Tactic : TACTIC =
struct

  type term = Syntax.t
  type name = Syntax.Variable.t
  type label = Syntax.Variable.t
  type level = Level.t
  type world = Development.t

  datatype t
    = LEMMA of world * label
    | UNFOLD of world * label list
    | CUSTOM_TACTIC of world * label
    | WITNESS of term
    | HYPOTHESIS of int
    | EQ_SUBST of {left : term,
                   right : term,
                   level : level option}
    | HYP_SUBST of {dir : Dir.dir,
                    index : int,
                    domain : term,
                    level : level option}
    | INTRO of {term : term option,
                freshVariable : name option,
                level : level option}
    | ELIM of {target : int,
               term : term option,
               names : name list}
    | EQ_CD of {names : name list,
                terms : term list,
                level : level option}
    | EXT of {freshVariable : name option,
              level : level option}
    | CUM of level option
    | AUTO
    | MEM_CD
    | ASSUMPTION
    | SYMMETRY
    | TRY of t
    | REPEAT of t
    | ORELSE of t list
    | ID
    | FAIL
    | TRACE of string
end
