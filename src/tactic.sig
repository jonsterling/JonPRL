signature TACTIC =
sig
    type term
    type name
    type label
    type level
    type world

    (* TODO: Can we avoid duplicating this?
     * Split this out of the big ctt.sig signature perhaps?
     *)
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
