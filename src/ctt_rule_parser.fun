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

  val parse_tm =
    middle (symbol "[") ParseSyntax.parse_abt (symbol "]")
      || middle (symbol "⌊") ParseSyntax.parse_abt (symbol "⌋")

  val parse_unit_elim =
    symbol "unit-elim"
      && brackets parse_name
      astac UnitElim

  val parse_prod_eq =
    symbol "prod-eq"
      && opt (brackets parse_name)
      astac ProdEq

  val parse_prod_intro =
    symbol "prod-intro"
      && parse_tm
      && opt (brackets parse_name)
      && opt parse_level
      astac (ProdIntro o flat3)

  val parse_prod_elim =
    symbol "prod-elim"
      && brackets (parse_name && opt (comma >> parse_name << comma && parse_name))
      astac ProdElim

  val parse_pair_eq =
    symbol "pair-eq"
      && opt (brackets parse_name) && opt parse_level
      astac PairEq

  val parse_spread_eq =
    symbol "spread-eq"
      && opt parse_tm
         && opt parse_tm
         && opt (brackets (parse_name && parse_name && parse_name))
      astac (fn (M, (N, names)) => SpreadEq (M, N, Option.map flat3 names))

  val parse_fun_eq =
    symbol "fun-eq"
      && opt (brackets parse_name)
      astac FunEq

  val parse_fun_intro =
    symbol "fun-intro"
      && opt (brackets parse_name) && opt parse_level
      astac FunIntro

  val parse_fun_elim =
    symbol "fun-elim"
      && brackets parse_name
         && parse_tm
         && opt (brackets (comma >> parse_name << comma && parse_name))
      astac (FunElim o flat3)

  val parse_lam_eq =
    symbol "lam-eq"
      && opt (brackets parse_name)
         && opt parse_level
      astac LamEq

  val parse_ap_eq =
    symbol "ap-eq"
      && opt parse_tm
      astac ApEq

  val parse_isect_eq =
    symbol "isect-eq"
      && opt (brackets parse_name)
      astac IsectEq

  val parse_isect_intro =
    symbol "isect-intro"
      && opt (brackets parse_name) && opt parse_level
      astac IsectIntro

  val parse_isect_elim =
    symbol "isect-elim"
      && brackets parse_name
         && parse_tm
         && opt (brackets (parse_name && parse_name))
      astac (IsectElim o flat3)

  val parse_isect_member_eq =
    symbol "isect-member-eq"
      && opt (brackets parse_name) && opt parse_level
      astac IsectMemberEq

  val parse_isect_member_case_eq =
    symbol "isect-member-case-eq"
      && ((parse_tm && parse_tm wth Sum.INL) || parse_tm wth Sum.INR)
      astac (fn Sum.INL (M,N) => IsectMemberCaseEq (SOME M, N)
              | Sum.INR M => IsectMemberCaseEq (NONE, M))

  val parse_witness =
    symbol "witness"
      && parse_tm
      astac Witness

  val parse_hypothesis =
    symbol "hypothesis"
      && brackets parse_name
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
      && brackets parse_name
      && parse_tm && opt parse_level
      astac (HypEqSubst o flat4)

  val parse_lemma =
    symbol "lemma"
      && brackets parse_name
      wth (fn (name, lbl) => fn st => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Lemma (st, lbl)))

  val parse_unfold =
    symbol "unfold"
      && brackets parse_name
      wth (fn (name, lbl) => fn st => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Unfold (st, lbl)))

  val parse_custom_tactic =
    symbol "refine"
      >> brackets parse_name
      wth (fn lbl => fn st => fn (pos : Pos.t) =>
            Lcf.annotate ({name = Syntax.Variable.to_string lbl, pos = pos}, Development.lookup_tactic st lbl))

  val parse_subset_eq =
    symbol "subset-eq"
      && opt (brackets parse_name)
      astac SubsetEq

  val parse_subset_intro =
    symbol "subset-intro"
      && parse_tm
      && opt (brackets parse_name)
      && opt parse_level
      astac (SubsetIntro o flat3)

  val parse_subset_elim =
    symbol "subset-elim"
      && brackets parse_name
      && opt (brackets (parse_name << comma && parse_name))
      astac SubsetElim

  val parse_subset_member_eq =
    symbol "subset-member-eq"
      && opt (brackets parse_name)
      && opt parse_level
      astac SubsetMemberEq

  val extensional_parse =
    symbol "auto" astac_ Auto
      || parse_cum
      || symbol "eq-eq" astac_ EqEq
      || symbol "univ-eq" astac_ UnivEq
      || symbol "void-eq" astac_ VoidEq
      || symbol "void-elim" astac_ VoidElim
      || symbol "unit-eq" astac_ UnitEq
      || symbol "unit-intro" astac_ UnitIntro
      || parse_unit_elim
      || symbol "ax-eq" astac_ AxEq
      || parse_prod_eq || parse_prod_intro || parse_prod_elim || parse_pair_eq || parse_spread_eq
      || parse_fun_eq || parse_fun_intro || parse_fun_elim || parse_lam_eq || parse_ap_eq
      || parse_isect_eq || parse_isect_intro || parse_isect_elim || parse_isect_member_eq || parse_isect_member_case_eq
      || symbol "mem-unfold" astac_ MemUnfold
      || symbol "assumption" astac_ Assumption
      || symbol "symmetry" astac_ EqSym
      || symbol "hyp-eq" astac_ HypEq
      || parse_witness
      || parse_hyp_subst
      || parse_eq_subst
      || parse_subset_eq
      || parse_subset_intro
      || parse_subset_elim
      || parse_subset_member_eq

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

