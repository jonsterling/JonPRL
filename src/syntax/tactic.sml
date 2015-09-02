structure Tactic : TACTIC =
struct
  type term = Syntax.t
  type name = Syntax.Variable.t
  type label = string
  type operator = Syntax.Operator.t
  type level = Level.t
  type meta = TacticMetadata.metadata
  type hyp = name HypSyn.t

  datatype ctx_pattern = CtxPattern of {goal : term, hyps : (name * term) list}

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
                    domain : term option} * meta
    | CHYP_SUBST of {dir : Dir.dir,
                     index : hyp,
                     domain : term option} * meta
    | INTRO of {term : term option,
                rule : int option,
                freshVariable : name option,
                level : level option} * meta
    | ELIM of {target : hyp,
               term   : term option,
               names  : name list,
               level  : level option} * meta
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
    | UNHIDE of hyp * meta
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
  and branch = Branch of {pendingSubst : (name * term) list, body : t}


  fun branch t = Branch {pendingSubst = [], body = t}

  structure Rebind = Rebind(Syntax)
  fun substBranch terms (Branch {pendingSubst, body}) =
    let
      fun join (sol1, sol2) =
        let
          fun eq ((v, _), (v', _)) = Syntax.Variable.eq (v, v')
        in
          sol2 @
          List.filter (fn x => not (List.exists (fn y => eq (x, y)) sol2)) sol1
        end

      val subst = join (pendingSubst, terms)
      fun apply e = List.foldl (fn ((v, e'), e) => Syntax.subst e' v e)
                               (Rebind.rebind (List.map #1 subst) e)
                               subst
      fun applyName (v : name) : name =
        let
          val tO =
            Option.map #2 (List.find ((fn (v', _) => Syntax.Variable.eq (v, v'))) subst)
        in
          case tO of
              NONE => v
            | SOME e =>
              case Syntax.out e of
                  Syntax.` v' => v'
                | _ => raise Fail "Impossible! Called substBranch on bad subst"
        end

      fun applyHyp (HypSyn.NAME v) =
            let
              val Syntax.` v' = Syntax.out (apply (Syntax.`` v))
            in
              HypSyn.NAME v'
            end
        | applyHyp h = h

      fun go t =
        case t of
            WITNESS (term, meta) => WITNESS (apply term, meta)
          | EQ_SUBST ({equality, domain, level}, meta) =>
            EQ_SUBST ({equality = apply equality,
                       domain = apply domain,
                       level = level}, meta)
          | HYP_SUBST ({dir, index, domain, level}, meta) =>
            HYP_SUBST ({dir = dir,
                        index = applyHyp index,
                        domain = apply domain,
                        level = level}, meta)
          | CEQ_SUBST ({equality, domain}, meta) =>
            CEQ_SUBST ({equality = apply equality,
                        domain = Option.map apply domain}, meta)
          | CHYP_SUBST ({dir, index, domain}, meta) =>
            CHYP_SUBST ({dir = dir,
                         index = applyHyp index,
                         domain = Option.map apply domain}, meta)
          | INTRO ({term, rule, freshVariable, level}, meta) =>
            INTRO ({term = Option.map apply term,
                    rule = rule,
                    freshVariable = freshVariable,
                    level = level}, meta)
          | ELIM ({target, term, names, level}, meta) =>
            ELIM ({target = applyHyp target,
                   term = Option.map apply term,
                   names = names,
		   level = level}, meta)
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
                                 Branch {pendingSubst = join (pendingSubst, subst),
                                         body = body}))
                            branches)
          | TRY t => TRY (go t)
          | LIMIT t => LIMIT (go t)
          | ORELSE (ts, meta) => ORELSE (List.map go ts, meta)
          | COMPLETE (t, meta) => COMPLETE (go t, meta)
          | BOTTOM_DIVERGES (h, meta) => BOTTOM_DIVERGES (applyHyp h, meta)
	  | ASSUME_HAS_VALUE ({name,level}, meta) => ASSUME_HAS_VALUE ({name = name, level = level}, meta)
          | HYPOTHESIS (h, meta) => HYPOTHESIS (applyHyp h, meta)
          | THIN (h, meta) => THIN (applyHyp h, meta)
          | ON_CLASS (c, t) => ON_CLASS (c, go t)
          | t => t
      and goPat (CtxPattern {goal, hyps}) =
          CtxPattern {goal = apply goal,
                      hyps = List.map (fn (v, e) => (applyName v, apply e)) hyps}
    in
      go body
    end

  val listOfTactics =
    ["intro [TERM]? #NUM? <NAME*>?",
     "elim (#NUM | <NAME>) [TERM]? <NAME*>?",
     "unhide (#NUM | <NAME>)",
     "eq-cd [TERM*]? <NAME*>? @LEVEL?",
     "eq-eq-base",
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
     "reduce-equand DIR",
     "lemma <NAME>",
     "cut-lemma <NAME> <NAME>?",
     "wf-lemma <NAME>",
     "unfold <(NAME @NUM)+>",
     "witness [TERM]",
     "hypothesis (#NUM | <NAME>)",
     "assume-has-value",
     "bot-div (#NUM | <NAME>)",
     "subst [TERM] [TERM] @NUM?",
     "hyp-subst (←|→) (#NUM | <NAME>) [TERM] @NUM?",
     "csubst [TERM] [TERM]? @NUM?",
     "chyp-subst (←|→) (#NUM | <NAME>) [TERM]? @NUM?",
     "id",
     "fail",
     "fiat",
     "trace \"MESSAGE\"",
     "cum @LEVEL?",
     "focus NUM #{TACTIC}",
     "progress {TACTIC}",
     "main {TACTIC}",
     "aux {TACTIC}",
     "thin (#NUM | <NAME>)",
     "bhyp (#NUM | <NAME>)",
     "resource RESOURCE"]
end
