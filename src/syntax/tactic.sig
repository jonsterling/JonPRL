signature TACTIC =
sig
    type term
    type name
    type label
    type level
    type operator
    type meta = TacticMetadata.metadata
    type hyp = name HypSyn.t

    type branch
    datatype ctx_pattern = CtxPattern of {goal : term,
                                          hyps : (name * term) list}

    datatype t =
        LEMMA of operator * meta
      | BHYP of hyp * meta
      | UNFOLD of (operator * level option) list * meta
      | CUSTOM_TACTIC of label * meta
      | WITNESS of term * meta
      | HYPOTHESIS of hyp * meta
      | EQ_SUBST of {equality : term,
                     domain : term,
                     level : level option} * meta
      | HYP_SUBST of {dir : Dir.dir,
                      index : hyp,
                      domain : term,
                      level : level option} * meta
      | CEQ_SUBST of {equality : term,
                      domain : term} * meta
      | CHYP_SUBST of {dir : Dir.dir,
                       index : hyp,
                       domain : term} * meta
      | INTRO of {term : term option,
                  rule : int option,
                  freshVariable : name option,
                  level : level option} * meta
      | ELIM of {target : hyp,
                 term : term option,
                 names : name list} * meta
      | EQ_CD of {names : name list,
                  terms : term list,
                  level : level option} * meta
      | EXT of {freshVariable : name option,
                level : level option} * meta
      | CUM of level option * meta
      | AUTO of int option * meta
      | REDUCE of int option * meta
      | ASSUMPTION of meta
      | ASSERT of {assertion : term,
                   name : name option} * meta
      | CUT_LEMMA of operator * name option * meta
      | WF_LEMMA of operator * meta
      | SYMMETRY of meta
      | CEQUAL_SYM of meta
      | CEQUAL_STEP of meta
      | CEQUAL_STRUCT of meta
      | CEQUAL_APPROX of meta
      | APPROX_REFL of meta
      | BOTTOM_DIVERGES of hyp * meta
      | ASSUME_HAS_VALUE of {name : name option, level : level option} * meta
      | EQ_EQ_BASE of meta
      | TRY of t
      | PROGRESS of t
      | LIMIT of t
      | ORELSE of t list * meta
      | THEN of then_tactic list
      | PRUNE of t
      | ID of meta
      | FAIL of meta
      | TRACE of string * meta
      | COMPLETE of t * meta
      | MATCH of (ctx_pattern * branch) list
      | THIN of hyp * meta
      | FIAT of meta
      | REDUCE_EQUAND of Dir.dir * meta
      | ON_CLASS of Goal.class * t
      | RESOURCE of Resource.t * meta
    and then_tactic =
        APPLY of t
      | LIST of t list
      | FOCUS of int * t

    val branch : t -> branch
    val substBranch : (name * term) list -> branch -> t
    val listOfTactics : string list
end
