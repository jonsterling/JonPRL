functor TacticEval(structure T : PROGRESS_TACTICALS
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

  fun eval t =
    case t of
        LEMMA (wld, lbl) => Lemma (wld, lbl)
      | UNFOLD (wld, lbls) => Unfolds (wld, lbls)
      | CUSTOM_TACTIC (wld, lbl) => D.lookupTactic wld lbl
      | WITNESS t => Witness t
      | HYPOTHESIS i => Hypothesis i
      | EQ_SUBST {left, right, level} => EqSubst (left, right, level)
      | HYP_SUBST {dir, index, domain, level} =>
        HypEqSubst (dir, index, domain, level)
      | INTRO {term, freshVariable, level} =>
        Intro {term = term, freshVariable = freshVariable, level = level}
      | ELIM {target, term, names} =>
        Elim {target = target, term = term, names = names}
      | EQ_CD {names, terms, level} =>
        EqCD {names = names, terms = terms, level = level}
      | EXT {freshVariable, level} =>
        Ext {freshVariable = freshVariable, level = level}
      | CUM l => Cum l
      | AUTO => To.Auto
      | MEM_CD => MemCD
      | ASSUMPTION => Assumption
      | SYMMETRY => EqSym
      | TRY tac => T.TRY (eval tac)
      | REPEAT tac => T.PROGRESS (eval tac)
      | ORELSE tacs => List.foldl T.ORELSE T.ID (map eval tacs)
      | ID => T.ID
      | FAIL => T.FAIL
      | TRACE msg => T.TRACE msg
end
