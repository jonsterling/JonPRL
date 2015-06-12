functor CttRuleParser
  (structure Lcf : ANNOTATED_LCF where type metadata = TacticMetadata.metadata
   structure Ctt : CTT_UTIL where type Development.Telescope.Label.t = string
   structure Operator : PARSE_OPERATOR
    where type env = Ctt.Development.label -> int vector
   sharing type Ctt.Lcf.goal = Lcf.goal
   sharing type Ctt.Lcf.evidence = Lcf.evidence
   sharing Ctt.Syntax.Operator = Operator):
sig
  structure Lcf : ANNOTATED_LCF
  type env = Ctt.Development.t
  val parse_rule : env -> Lcf.tactic CharParser.charParser
end =
struct
  structure AnnLcf = Lcf
  structure ParseSyntax = ParseAbt
    (structure Syntax = AbtUtil(Ctt.Syntax)
     structure Operator = Operator)
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

  type env = Development.t

  val parse_int =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parse_level =
    lexeme (symbol "@" >> parse_int)

  val parse_index =
    lexeme (symbol "#" >> parse_int)

  fun parse_opt p =
    symbol "_" return NONE
      || p wth SOME

  val parse_name =
    identifier
      wth Syntax.Variable.named

  fun decorate_tac tac =
    fn (name, args) => fn (pos : Pos.t) =>
      Lcf.annotate ({name = name, pos = pos}, tac args)

  fun name_tac name tac =
    fn (pos : Pos.t) =>
      Lcf.annotate ({name = name, pos = pos}, tac)

  type 'a intensional_parser = Development.t -> 'a charParser
  type tactic_parser = (Pos.t -> tactic) intensional_parser

  val parse_tm : term intensional_parser =
    squares o ParseSyntax.parse_abt [] o Development.lookup_operator

  val parse_cum : tactic_parser =
    fn D => symbol "cum"
      && opt parse_level
      wth (fn (name, k) => name_tac name (Cum k))

  val parse_witness : tactic_parser =
    fn D => symbol "witness"
      && parse_tm D
      wth (fn (name, tm) =>
        name_tac name (Witness tm))

  val parse_hypothesis : tactic_parser =
    fn D => symbol "hypothesis"
      && parse_index
      wth (fn (name, i) =>
        name_tac name (Hypothesis i))

  val parse_eq_subst : tactic_parser =
    fn D => symbol "subst"
      && parse_tm D && parse_tm D && opt parse_level
      wth (fn (name, (M, (N, k))) =>
        name_tac name (EqSubst (M, N, k)))

  val parse_dir =
    (symbol "→" || symbol "->") return RIGHT
      || (symbol "←" || symbol "<-") return LEFT

  val parse_hyp_subst : tactic_parser =
    fn D => symbol "hyp-subst"
      && parse_dir
      && parse_index
      && parse_tm D && opt parse_level
      wth (fn (name, (dir, (i, (M, k)))) =>
        name_tac name (HypEqSubst (dir, i, M, k)))

  val parse_intro_args : intro_args intensional_parser =
    fn D => opt (parse_tm D)
      && opt (brackets parse_name)
      && opt parse_level
      wth (fn (tm, (z, k)) =>
            {term = tm,
             fresh_variable = z,
             level = k})

  val parse_names =
    opt (brackets (commaSep1 parse_name))
    wth (fn SOME xs => xs
          | NONE => [])

  val parse_elim_args : elim_args intensional_parser=
    fn D => parse_index
      && opt (parse_tm D)
      && parse_names
      wth (fn (i, (M, names)) =>
            {target = i,
             term = M,
             names = names})

  val parse_terms : term list intensional_parser =
    fn D => opt (squares (commaSep1 (ParseSyntax.parse_abt [] (Development.lookup_operator D))))
    wth (fn oxs => getOpt (oxs, []))

  val parse_eq_cd_args : eq_cd_args intensional_parser =
    fn D => (parse_terms D)
      && parse_names
      && opt parse_level
      wth (fn (Ms, (xs, k)) => {names = xs, terms = Ms, level = k})

  val parse_intro =
    fn D => symbol "intro"
      && parse_intro_args D
      wth (fn (name, args) => name_tac name (Intro args))

  val parse_elim =
    fn D => symbol "elim"
      && parse_elim_args D
      wth (fn (name, args) => name_tac name (Elim args))


  val parse_eq_cd =
    fn D => symbol "eq-cd"
      && (parse_eq_cd_args D)
      wth (fn (name, args) => name_tac name (EqCD args))

  val parse_symmetry : tactic_parser =
    fn D => symbol "symmetry"
      wth (fn name => name_tac name EqSym)

  val parse_assumption : tactic_parser =
    fn D => symbol "assumption"
      wth (fn name => name_tac name Assumption)

  val parse_mem_cd : tactic_parser =
    fn D => symbol "mem-cd"
      wth (fn name => name_tac name MemCD)

  val parse_auto : tactic_parser =
    fn D => symbol "auto"
      wth (fn name => name_tac name Auto)

  val parse_lemma : tactic_parser =
    fn D => symbol "lemma"
      && brackets identifier
      wth (fn (name, lbl) => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Lemma (D, lbl)))

  val parse_unfold : tactic_parser =
    fn D => symbol "unfold"
      && brackets (separate identifier whiteSpace)
      wth (fn (name, lbls) => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Unfolds (D, lbls)))

  val parse_custom_tactic : tactic_parser =
    fn D => symbol "refine"
      >> brackets identifier
      wth (fn lbl => fn (pos : Pos.t) =>
            Lcf.annotate ({name = lbl, pos = pos}, fn goal =>
              Development.lookup_tactic D lbl goal))

  fun tactic_parsers D =
    parse_lemma D
      || parse_unfold D
      || parse_custom_tactic D
      || parse_witness D
      || parse_hypothesis D
      || parse_eq_subst D
      || parse_hyp_subst D
      || parse_intro D
      || parse_elim D
      || parse_eq_cd D
      || parse_cum D
      || parse_auto D
      || parse_mem_cd D
      || parse_assumption D
      || parse_symmetry D

  val parse_rule : Development.t -> tactic charParser =
    fn D => !! (tactic_parsers D)
    wth (fn (t, pos) => t pos)

end

structure CttRuleParser = CttRuleParser
  (structure Operator = Syntax.ParseOperator
   structure Ctt = CttUtil
   structure Lcf = AnnotatedLcf
   structure Development = Development
   structure Syntax = Syntax)

structure CttScript = TacticScript
  (struct
    structure LcfApart = Lcf
    open CttRuleParser
   end)

