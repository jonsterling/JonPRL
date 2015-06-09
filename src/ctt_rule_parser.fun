functor CttRuleParser
  (structure Lcf : ANNOTATED_LCF where type metadata = TacticMetadata.metadata
   structure Syntax : PARSE_ABT
   structure Ctt : CTT_UTIL
    where Lcf = Lcf
    where Syntax = Syntax):
sig
  structure Lcf : ANNOTATED_LCF
  type state = Ctt.Development.t
  val parse_rule : (state -> Lcf.tactic) CharParser.charParser
end =
struct
  structure AnnLcf = Lcf
  structure ParseSyntax = Syntax
  structure Tacticals = Tacticals (Lcf)
  open Ctt Lcf Tacticals ParserCombinators CharParser
  structure Lcf = AnnLcf

  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  structure LangDef :> LANGUAGE_DEF =
  struct
    type scanner = char CharParser.charParser
    val commentStart = NONE
    val commentEnd = NONE
    val commentLine = NONE
    val nestedComments = false

    val identLetter = CharParser.letter || CharParser.oneOf (String.explode "'_-ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσΤτΥυΦφΧχΨψΩω") || CharParser.digit
    val identStart = identLetter
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = []
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TP = TokenParser (LangDef)
  open TP Rules

  type state = Development.t

  val parse_level =
    symbol "@"
      >> repeat1 digit
        wth valOf o Int.fromString o String.implode

  fun parse_opt p =
    symbol "_" return NONE
      || p wth SOME

  val parse_name =
    identifier
      wth Syntax.Variable.named

  fun decorate_tac tac =
    fn (name, args) => fn (pos : Pos.t) =>
      Lcf.annotate ({name = name, pos = pos}, tac args)

  fun astac (p, tac) = p wth (decorate_tac tac)
  infix 2 astac

  fun astac_ (p : string charParser, tac : tactic) : (Pos.t -> tactic) charParser =
    p wth (fn name => fn (pos : Pos.t) =>
      Lcf.annotate ({name = name, pos = pos}, tac))
  infix 2 astac_

  val parse_cum =
    symbol "cum"
      && opt parse_level
      astac Cum

  fun angles p =
    brackets p
      || middle (symbol "〈") p  (symbol "〉")

  fun quote_squares p =
    middle (symbol "[") p (symbol "]")
      || middle (symbol "⌊") p (symbol "⌋")

  val parse_tm =
    quote_squares ParseSyntax.parse_abt

  val parse_witness =
    symbol "witness"
      && parse_tm
      astac Witness

  val parse_hypothesis =
    symbol "hypothesis"
      && angles parse_name
      astac Hypothesis

  val parse_eq_subst =
    symbol "subst"
      && parse_tm && parse_tm && opt parse_level
      astac (EqSubst o flat3)

  val parse_dir =
    (symbol "→" || symbol "->") return RIGHT
      || (symbol "←" || symbol "<-") return LEFT

  val parse_hyp_subst =
    symbol "hyp-subst"
      && parse_dir
      && angles parse_name
      && parse_tm && opt parse_level
      astac (HypEqSubst o flat4)

  val parse_lemma =
    symbol "lemma"
      && angles parse_name
      wth (fn (name, lbl) => fn st => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Lemma (st, lbl)))

  val parse_unfold =
    symbol "unfold"
      && angles parse_name
      wth (fn (name, lbl) => fn st => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Unfold (st, lbl)))

  val parse_custom_tactic =
    symbol "refine"
      >> angles parse_name
      wth (fn lbl => fn st => fn (pos : Pos.t) =>
            Lcf.annotate ({name = Syntax.Variable.to_string lbl, pos = pos}, fn goal =>
              Development.lookup_tactic st lbl goal))

  val parse_intro_args =
    opt parse_tm
      && opt (angles parse_name)
      && opt parse_level
      wth (fn (tm, (z, k)) => {term = tm, fresh_variable = z, level = k})

  val parse_intro =
    symbol "intro"
      && parse_intro_args
      astac Intro

  val parse_names =
    opt (angles (commaSep1 parse_name))
    wth (fn SOME xs => xs
          | NONE => [])

  val parse_elim_args =
    angles parse_name
      && opt parse_tm
      && parse_names
      wth (fn (z, (M, names)) => {target = z, term = M, names = names})

  val parse_elim =
    symbol "elim"
      && parse_elim_args
      astac Elim

  val parse_terms =
    opt (quote_squares (commaSep1 ParseSyntax.parse_abt))
    wth (fn SOME xs => xs
          | NONE => [])

  val parse_eq_cd_args =
    parse_terms
      && parse_names
      && opt parse_level
      wth (fn (Ms, (xs, k)) => {names = xs, terms = Ms, level = k})

  val parse_eq_cd =
    symbol "eq-cd"
      && parse_eq_cd_args
      astac EqCD

  val extensional_parse =
    symbol "auto" astac_ Auto
      || parse_intro
      || parse_elim
      || parse_eq_cd
      || parse_cum
      || symbol "mem-cd" astac_ MemCD
      || symbol "assumption" astac_ Assumption
      || symbol "symmetry" astac_ EqSym
      || parse_witness
      || parse_hyp_subst
      || parse_eq_subst

  val intensional_parse =
    parse_lemma
      || parse_unfold
      || parse_custom_tactic

  val parse_rule : (state -> tactic) charParser =
    !! (intensional_parse || extensional_parse wth (fn t => fn _ => t))
    wth (fn (t, pos) => fn st => t st pos)

end

structure CttRuleParser = CttRuleParser
  (structure Ctt = CttUtil
   structure Lcf = AnnotatedLcf
   structure Development = Development
   structure Syntax = Syntax)

structure CttScript = TacticScript (CttRuleParser)

