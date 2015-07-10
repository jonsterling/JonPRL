structure TacticEval :
sig
  exception RemainingSubgoals of Development.judgement list
  val eval : Development.world -> Tactic.t -> Ctt.tactic
end =
struct
  open Tactic
  open Ctt.Rules
  structure T = ProgressTacticals(Lcf)
  exception RemainingSubgoals = T.RemainingSubgoals

  fun an a t = AnnotatedLcf.annotate (a, t)

  fun eval wld t =
    case t of
        LEMMA (lbl, a) => an a (Lemma (wld, lbl))
      | UNFOLD (lbls, a) => an a (Unfolds (wld, lbls))
      | CUSTOM_TACTIC (lbl, a) =>
        an a (Development.lookupTactic wld lbl)
      | WITNESS (t, a) => an a (Witness t)
      | HYPOTHESIS (i, a) => an a (Hypothesis i)
      | EQ_SUBST ({equality, domain, level}, a) =>
        an a (EqSubst (equality, domain, level))
      | HYP_SUBST ({dir, index, domain, level}, a) =>
        an a (HypEqSubst (dir, index, domain, level))
      | CEQ_SUBST ({equality, domain}, a) =>
        an a (CEqSubst (equality, domain))
      | CHYP_SUBST ({dir, index, domain}, a) =>
        an a (HypCEqSubst (dir, index, domain))
      | INTRO ({term, rule, freshVariable, level}, a) =>
        an a (CttUtil.Intro {term = term,
                             rule = rule,
                             invertible = false,
                             freshVariable = freshVariable,
                             level = level})
      | ELIM ({target, term, names}, a) =>
        an a (CttUtil.Elim {target = target, term = term, names = names})
      | EQ_CD ({names, terms, level}, a) =>
        an a (CttUtil.EqCD {names = names,
                            invertible = false,
                            terms = terms,
                            level = level})
      | EXT ({freshVariable, level}, a) =>
        an a (CttUtil.Ext {freshVariable = freshVariable, level = level})
      | CUM (l, a) => an a (Cum l)
      | AUTO (oi, a) => an a (CttUtil.Auto oi)
      | REDUCE (i, a) => an a (CttUtil.Reduce i)
      | MEM_CD a => an a MemCD
      | ASSUMPTION a => an a Assumption
      | ASSERT ({assertion = t, name = name}, a) =>
        an a (Assert (t, name))
      | CUT_LEMMA (lbl, a) => an a (CttUtil.CutLemma (wld, lbl))
      | SYMMETRY a => an a EqSym
      | CEQUAL_SYM a => an a CEqSym
      | CEQUAL_STEP a => an a CEqStep
      | CEQUAL_STRUCT a => an a CEqStruct
      | CEQUAL_APPROX a => an a CEqApprox
      | APPROX_REFL a => an a ApproxRefl
      | TRY tac => T.TRY (eval wld tac)
      | LIMIT tac => T.LIMIT (eval wld tac)
      | ORELSE (tacs, a) => an a (List.foldl T.ORELSE T.FAIL (map (eval wld) tacs))
      | THEN ts =>
        List.foldl
          (fn (APPLY x, rest) => T.THEN (rest, eval wld x)
            | (LIST xs, rest) => T.THENL (rest, map (eval wld) xs)
            | (FOCUS (i, x), rest) => T.THENF (rest, i, eval wld x))
          T.ID
          ts
      | ID a => an a T.ID
      | FAIL a => an a T.FAIL
      | TRACE (msg, a) => an a (T.TRACE msg)
      | COMPLETE (t, a) => an a (T.COMPLETE (eval wld t))
end
