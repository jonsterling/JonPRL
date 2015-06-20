signature TACTIC =
sig
    structure TermSyn : ABT
    structure Label   : LABEL
    structure Level   : LEVEL

    (* TODO: Can we avoid duplicating this?
     * Split this out of the big ctt.sig signature perhaps?
     *)
    datatype dir = Left | Right
    datatype t
      = LEMMA of Label.t
      | UNFOLD of Label.t list
      | CUSTOM_TACTIC of Label.t
      | WITNESS of TermSyn.t
      | HYPOTHESIS of int
      | EQ_SUBST of {left : TermSyn.t,
                     right : TermSyn.t,
                     level : Level.t}
      | HYP_SUBST of {dir : dir,
                      index : int,
                      domain : TermSyn.t,
                      level : Level.t}
      | INTRO of {tm : TermSyn.t,
                  freshVariable : TermSyn.Variable.t,
                  level : Level.t}
      | ELIM of {target : int,
                 term : TermSyn.t,
                 names : TermSyn.Variable.t list}
      | EQ_CD of {names : TermSyn.Variable.t list,
                  terms : TermSyn.t list,
                  level : Level.t}
      | EXT of {freshVariable : TermSyn.Variable.t,
                level : Level.t}
      | CUM of Level.t
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
