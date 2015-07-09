structure Tactic : TACTIC =
struct

  type term = Syntax.t
  type name = Syntax.Variable.t
  type label = string
  type level = Level.t
  type meta = TacticMetadata.metadata

  datatype t =
      LEMMA of label * meta
    | UNFOLD of (label * level option) list * meta
    | CUSTOM_TACTIC of label * meta
    | WITNESS of term * meta
    | HYPOTHESIS of int * meta
    | EQ_SUBST of {left : term,
                   right : term,
                   level : level option} * meta
    | HYP_SUBST of {dir : Dir.dir,
                    index : int,
                    domain : term,
                    level : level option} * meta
    | CEQ_SUBST of {left : term,
                    right : term} * meta
    | CHYP_SUBST of {dir : Dir.dir,
                     index : int,
                     domain : term} * meta
    | INTRO of {term : term option,
                rule : int option,
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
    | AUTO of int option * meta
    | REDUCE of int option * meta
    | MEM_CD of meta
    | ASSUMPTION of meta
    | ASSERT of {assertion : term,
                 name : name option} * meta
    | CUT_LEMMA of label * meta
    | SYMMETRY of meta
    | CEQUAL_REFL of meta
    | CEQUAL_SYM of meta
    | CEQUAL_STEP of meta
    | CEQUAL_STRUCT of meta
    | CEQUAL_APPROX of meta
    | APPROX_REFL of meta
    | TRY of t
    | LIMIT of t
    | ORELSE of t list * meta
    | THEN of then_tactic list
    | ID of meta
    | FAIL of meta
    | TRACE of string * meta
    | COMPLETE of t * meta
  and then_tactic =
      APPLY of t
    | LIST of t list
    | FOCUS of int * t
end
