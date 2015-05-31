functor CttRuleParser
  (structure Lcf : LCF
   structure Syntax : PARSE_ABT
   structure Development : DEVELOPMENT where type label = string
   structure Ctt : CTT_UTIL
    where Development = Development
    where type tactic = Lcf.tactic
    where type term = Syntax.t
    where type name = Syntax.Variable.t):
sig
  structure Lcf : LCF
  type state = Development.t
  val parse_rule : (state -> Lcf.tactic) CharParser.charParser
end =
struct
  structure Lcf = Lcf

  structure Tacticals = Tacticals (Lcf)
  open Ctt Lcf Tacticals ParserCombinators CharParser
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

  exception XXX

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

  val parse_cum =
    symbol "cum"
      >> opt parse_level
      wth Cum

  val parse_tm =
    middle (symbol "[") Syntax.parse_abt (symbol "]")
      || middle (symbol "⌊") Syntax.parse_abt (symbol "⌋")

  val parse_unit_elim =
    symbol "unit-elim"
      >> brackets parse_name
      wth UnitElim

  val parse_squash_elim =
    symbol "squash-elim"
      >> brackets parse_name
      wth SquashElim

  val parse_prod_eq =
    symbol "prod-eq"
      >> opt (brackets parse_name)
      wth ProdEq

  val parse_prod_intro =
    symbol "prod-intro"
      >> parse_tm
      wth ProdIntro

  val parse_prod_elim =
    symbol "prod-elim"
      >> brackets (parse_name && opt (comma >> parse_name << comma && parse_name))
      wth (fn (x,st) => ProdElim x st)

  val parse_pair_eq =
    symbol "pair-eq"
      >> opt (brackets parse_name) && opt parse_level
      wth (fn (z, k) => PairEq z k)

  val parse_spread_eq =
    symbol "spread-eq"
      >> opt parse_tm
         && opt parse_tm
         && opt (brackets (parse_name && parse_name && parse_name))
      wth (fn (M, (N, names)) => SpreadEq M N (Option.map flat3 names))

  val parse_fun_eq =
    symbol "fun-eq"
      >> opt (brackets parse_name)
      wth FunEq

  val parse_fun_intro =
    symbol "fun-intro"
      >> opt (brackets parse_name) && opt parse_level
      wth (fn (z,k) => FunIntro z k)

  val parse_fun_elim =
    symbol "fun-elim"
      >> brackets parse_name
         && parse_tm
         && opt (brackets (comma >> parse_name << comma && parse_name))
      wth (fn (z, (M, st)) => FunElim z M st)

  val parse_lam_eq =
    symbol "lam-eq"
      >> opt (brackets parse_name)
         && opt parse_level
      wth (fn (z,k) => LamEq z k)

  val parse_ap_eq =
    symbol "ap-eq"
      >> opt parse_tm
      wth ApEq

  val parse_isect_eq =
    symbol "isect-eq"
      >> opt (brackets parse_name)
      wth IsectEq

  val parse_isect_intro =
    symbol "isect-intro"
      >> opt (brackets parse_name) && opt parse_level
      wth (fn (z,k) => IsectIntro z k)

  val parse_isect_elim =
    symbol "isect-elim"
      >> brackets parse_name
         && parse_tm
         && opt (brackets (parse_name && parse_name))
      wth (fn (z,(M,st)) => IsectElim z M st)

  val parse_isect_member_eq =
    symbol "isect-member-eq"
      >> opt (brackets parse_name) && opt parse_level
      wth (fn (z,k) => IsectMemberEq z k)

  val parse_isect_member_case_eq =
    symbol "isect-member-case-eq"
      >> ((parse_tm && parse_tm wth Sum.INL) || parse_tm wth Sum.INR)
      wth (fn Sum.INL (M,N) => IsectMemberCaseEq (SOME M) N
            | Sum.INR M => IsectMemberCaseEq NONE M)

  val parse_witness =
    symbol "witness"
      >> parse_tm
      wth Witness

  val parse_hypothesis =
    symbol "hypothesis"
      >> brackets parse_name
      wth Hypothesis

  val parse_eq_subst =
    symbol "subst"
      >> parse_tm && parse_tm && opt parse_level
      wth (fn (M, (N, k)) => EqSubst M N k)

  type state = Development.t

  val parse_lemma =
    symbol "lemma"
      >> brackets identifier
      wth (fn x => fn st => Lemma (st, x))

  val parse_unfold =
    symbol "unfold"
      >> brackets identifier
      wth (fn x => fn st => Unfold (st, x))

  val extensional_parse =
    symbol "auto" return Auto
      || parse_cum
      || symbol "eq-eq" return EqEq
      || symbol "univ-eq" return UnivEq
      || symbol "void-eq" return VoidEq
      || symbol "void-elim" return VoidElim
      || symbol "unit-eq" return UnitEq
      || symbol "unit-intro" return UnitIntro
      || parse_unit_elim
      || symbol "ax-eq" return AxEq
      || symbol "squash-eq" return SquashEq
      || symbol "squash-intro" return SquashIntro
      || parse_squash_elim
      || parse_prod_eq || parse_prod_intro || parse_prod_elim || parse_pair_eq || parse_spread_eq
      || parse_fun_eq || parse_fun_intro || parse_fun_elim || parse_lam_eq || parse_ap_eq
      || parse_isect_eq || parse_isect_intro || parse_isect_elim || parse_isect_member_eq || parse_isect_member_case_eq
      || symbol "mem-unfold" return MemUnfold
      || symbol "assumption" return Assumption
      || symbol "symmetry" return EqSym
      || symbol "hyp-eq" return HypEq
      || parse_witness
      || parse_eq_subst

  val intensional_parse =
    parse_lemma
      || parse_unfold

  val parse_rule = intensional_parse || extensional_parse wth (fn t => fn _ => t)

end

structure CttRuleParser = CttRuleParser
  (structure Ctt = CttUtil
   structure Lcf = Lcf
   structure Development = Development
   structure Syntax = Syntax)

structure CttScript = TacticScript (CttRuleParser)

