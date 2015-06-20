signature TACTIC =
sig
    type term
    type name
    type label
    type level
    type world
    type meta = TacticMetadata.metadata

    (* TODO: Can we avoid duplicating this?
     * Split this out of the big ctt.sig signature perhaps?
     *)
    datatype t
      = LEMMA of world * label * meta
      | UNFOLD of world * label list * meta
      | CUSTOM_TACTIC of world * label * meta
      | WITNESS of term * meta
      | HYPOTHESIS of int * meta
      | EQ_SUBST of {left : term,
                     right : term,
                     level : level option} * meta
      | HYP_SUBST of {dir : Dir.dir,
                      index : int,
                      domain : term,
                      level : level option} * meta
      | INTRO of {term : term option,
                  freshVariable : name option,
                  level : level option} * meta
      | ELIM of {target : int,
                 term : term option,
                 names : name list} * meta
      | EQ_CD of {names : name list,
                  terms : term list,
                  level : level option} * meta
      | EXT of {freshVariable : name option,
                level : level option} * meta
      | CUM of level option * meta
      | AUTO of meta
      | MEM_CD of meta
      | ASSUMPTION of meta
      | SYMMETRY of meta
      | TRY of t * meta
      | REPEAT of t
      | ORELSE of t list
      | THEN of t * t
      | THENL of t * t list
      | ID of meta
      | FAIL of meta
      | TRACE of string * meta
end
