functor TacticEval(structure Lcf : ANNOTATED_LCF
                      where type metadata = TacticMetadata.metadata
                   structure T : PROGRESS_TACTICALS
                      where type tactic   = Lcf.tactic
                   structure D : DEVELOPMENT
                      where type tactic = T.tactic
                   structure From : TACTIC
                      where type level = Level.t
                      where type world = D.t
                      where type label = D.label
                   structure To : CTT_UTIL
                      where type term   = From.term
                      where type name   = From.name
                      where type label  = From.label
                      where type world  = From.world
                      where type tactic = D.tactic) :
        sig
            val eval : From.t -> To.tactic
        end =
struct
  open From
  open To
  open Rules

  fun an a t = Lcf.annotate (a, t)

  fun eval t =
    case t of
        LEMMA (wld, lbl, a) => an a (Lemma (wld, lbl))
      | UNFOLD (wld, lbls, a) => an a (Unfolds (wld, lbls))
      | CUSTOM_TACTIC (wld, lbl, a) => an a (D.lookupTactic wld lbl)
      | WITNESS (t, a) => an a (Witness t)
      | HYPOTHESIS (i, a) => an a (Hypothesis i)
      | EQ_SUBST ({left, right, level}, a) =>
        an a (EqSubst (left, right, level))
      | HYP_SUBST ({dir, index, domain, level}, a) =>
        an a (HypEqSubst (dir, index, domain, level))
      | INTRO ({term, freshVariable, level}, a) =>
        an a (Intro {term = term,
                     freshVariable = freshVariable,
                     level = level})
      | ELIM ({target, term, names}, a) =>
        an a (Elim {target = target, term = term, names = names})
      | EQ_CD ({names, terms, level}, a) =>
        an a (EqCD {names = names, terms = terms, level = level})
      | EXT ({freshVariable, level}, a) =>
        an a (Ext {freshVariable = freshVariable, level = level})
      | CUM (l, a) => an a (Cum l)
      | AUTO a => an a To.Auto
      | MEM_CD a => an a MemCD
      | ASSUMPTION a => an a Assumption
      | SYMMETRY a => an a EqSym
      | TRY (tac, a) => an a (T.TRY (eval tac))
      | REPEAT tac => T.LIMIT (eval tac)
      | ORELSE tacs => List.foldl T.ORELSE T.FAIL (map eval tacs)
      | THEN (l, r) => T.THEN (eval l, eval r)
      | THENL (l, rs)  => T.THENL (eval l, map eval rs)
      | ID a => an a T.ID
      | FAIL a => an a T.FAIL
      | TRACE (msg, a) => an a (T.TRACE msg)
end
