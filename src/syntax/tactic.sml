structure Tactic : TACTIC =
struct

  type term = Syntax.t
  type name = Syntax.Variable.t
  type label = string
  type level = Level.t
  type meta = TacticMetadata.metadata

  datatype ctx_pattern = CtxPattern of {goal : term, hyps : term list}

  datatype t =
      LEMMA of label * meta
    | UNFOLD of (label * level option) list * meta
    | CUSTOM_TACTIC of label * meta
    | WITNESS of term * meta
    | HYPOTHESIS of int * meta
    | EQ_SUBST of {equality : term,
                   domain : term,
                   level : level option} * meta
    | HYP_SUBST of {dir : Dir.dir,
                    index : int,
                    domain : term,
                    level : level option} * meta
    | CEQ_SUBST of {equality : term,
                    domain : term} * meta
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
    | ASSUMPTION of meta
    | ASSERT of {assertion : term,
                 name : name option} * meta
    | CUT_LEMMA of label * meta
    | SYMMETRY of meta
    | CEQUAL_SYM of meta
    | CEQUAL_STEP of meta
    | CEQUAL_STRUCT of meta
    | CEQUAL_APPROX of meta
    | APPROX_REFL of meta
    | BOTTOM_DIVERGES of int * meta
    | TRY of t
    | LIMIT of t
    | ORELSE of t list * meta
    | THEN of then_tactic list
    | ID of meta
    | FAIL of meta
    | TRACE of string * meta
    | COMPLETE of t * meta
    | MATCH of (ctx_pattern * branch) list
  and then_tactic =
      APPLY of t
    | LIST of t list
    | FOCUS of int * t
  and branch = Branch of {pendingSubst : (name * term) list, body : t}

  fun substBranch terms (Branch {pendingSubst, body}) =
    let
      fun join (xs, ys) =
        xs @
        List.filter
          (fn (v, _) => List.all
              (fn (v', _) => not (Syntax.Variable.eq (v, v'))) xs)
          ys
      val subst = join (terms, pendingSubst)
      fun apply e = List.foldl (fn ((v, e'), e) => Syntax.subst e' v e) e subst
      fun go t =
        case t of
            WITNESS (term, meta) => WITNESS (apply term, meta)
          | EQ_SUBST ({equality, domain, level}, meta) =>
            EQ_SUBST ({equality = apply equality,
                       domain = apply domain,
                       level = level}, meta)
          | HYP_SUBST ({dir, index, domain, level}, meta) =>
            HYP_SUBST ({dir = dir,
                        index = index,
                        domain = apply domain,
                        level = level}, meta)
          | CEQ_SUBST ({equality, domain}, meta) =>
            CEQ_SUBST ({equality = apply equality,
                        domain = apply domain}, meta)
          | CHYP_SUBST ({dir, index, domain}, meta) =>
            CHYP_SUBST ({dir = dir,
                         index = index,
                         domain = apply domain}, meta)
          | INTRO ({term, rule, freshVariable, level}, meta) =>
            INTRO ({term = Option.map apply term,
                    rule = rule,
                    freshVariable = freshVariable,
                    level = level}, meta)
          | ELIM ({target, term, names}, meta) =>
            ELIM ({target = target,
                   term = Option.map apply term,
                   names = names}, meta)
          | EQ_CD ({names, terms, level}, meta) =>
            EQ_CD ({names = names,
                    terms = List.map apply terms,
                    level = level}, meta)
          | ASSERT ({assertion, name}, meta) =>
            ASSERT ({assertion = apply assertion,
                     name = name}, meta)
          | THEN ts =>
            THEN (List.map (fn (APPLY t) => APPLY (go t)
                            | (LIST ts) => LIST (List.map go ts)
                            | (FOCUS (i, t)) => FOCUS (i, go t))
                           ts)
          | MATCH branches =>
            MATCH (List.map (fn (pat, Branch {pendingSubst, body}) =>
                                (goPat pat,
                                 Branch {pendingSubst = join (subst, pendingSubst),
                                         body = body}))
                            branches)
          | TRY t => TRY (go t)
          | LIMIT t => LIMIT (go t)
          | ORELSE (ts, meta) => ORELSE (List.map go ts, meta)
          | COMPLETE (t, meta) => COMPLETE (go t, meta)
          | t => t
      and goPat (CtxPattern {goal, hyps}) =
          CtxPattern {goal = apply goal, hyps = List.map apply hyps}
    in
      raise Fail ""
    end

  val listOfTactics =
    ["intro [TERM]? #NUM? <NAME*>?",
     "elim #NUM [TERM]? <NAME*>?",
     "eq-cd [TERM*]? <NAME*>? @LEVEL?",
     "ext <NAME>? @LEVEL?",
     "symmetry",
     "capprox",
     "creflexivty",
     "areflexivty",
     "csymmetry",
     "step",
     "cstruct",
     "assumption",
     "assert [TERM] <NAME>?",
     "auto NUM?",
     "reduce NUM?",
     "lemma <NAME>",
     "cut-lemma <NAME>",
     "unfold <(NAME @NUM)+>",
     "witness [TERM]",
     "hypothesis #NUM",
     "bot-div #NUM",
     "hyp-subst (←|→) #NUM [TERM] @NUM?",
     "id",
     "fail",
     "trace \"MESSAGE\"",
     "cum @NUM?",
     "focus NUM #{TACTIC}"]
end
