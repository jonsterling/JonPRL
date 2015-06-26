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
      | EQ_SUBST ({left, right, level}, a) =>
        an a (EqSubst (left, right, level))
      | HYP_SUBST ({dir, index, domain, level}, a) =>
        an a (HypEqSubst (dir, index, domain, level))
      | CEQ_SUBST ({left, right}, a) =>
        an a (CEqSubst (left, right))
      | CHYP_SUBST ({dir, index, domain}, a) =>
        an a (HypCEqSubst (dir, index, domain))
      | INTRO ({term, rule, freshVariable, level}, a) =>
        an a (CttUtil.Intro {term = term,
                             rule = rule,
                             freshVariable = freshVariable,
                             level = level})
      | ELIM ({target, term, names}, a) =>
        an a (CttUtil.Elim {target = target, term = term, names = names})
      | EQ_CD ({names, terms, level}, a) =>
        an a (CttUtil.EqCD {names = names, terms = terms, level = level})
      | EXT ({freshVariable, level}, a) =>
        an a (CttUtil.Ext {freshVariable = freshVariable, level = level})
      | CUM (l, a) => an a (Cum l)
      | AUTO a => an a CttUtil.Auto
      | REDUCE (i, a) => an a (CttUtil.Reduce i)
      | MEM_CD a => an a MemCD
      | ASSUMPTION a => an a Assumption
      | ASSERT ({assertion = t, name = name}, a) =>
        an a (Assert (t, name))
      | SYMMETRY a => an a EqSym
      | CEQUAL_REFL a => an a CEqRefl
      | CEQUAL_SYM a => an a CEqSym
      | CEQUAL_STEP a => an a CEqStep
      | TRY tac => T.TRY (eval wld tac)
      | LIMIT tac => T.LIMIT (eval wld tac)
      | ORELSE (tacs, a) => an a (List.foldl T.ORELSE T.FAIL (map (eval wld) tacs))
      | THEN ts =>
        List.foldl
          (fn (Sum.INL x, rest) => T.THEN (rest, (eval wld) x)
            | (Sum.INR xs, rest) => T.THENL (rest, map (eval wld) xs))
          T.ID
          ts
      | ID a => an a T.ID
      | FAIL a => an a T.FAIL
      | TRACE (msg, a) => an a (T.TRACE msg)
      | COMPLETE (t, a) => an a (T.COMPLETE (eval wld t))
end
