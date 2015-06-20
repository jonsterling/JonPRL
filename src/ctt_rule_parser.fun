functor CttRuleParser
  (structure Lcf : ANNOTATED_LCF
     where type metadata = TacticMetadata.metadata

   structure Development : DEVELOPMENT
     where type judgement = Lcf.goal
     where type evidence = Lcf.evidence
     where type tactic = Lcf.tactic
     where type Telescope.Label.t = string

   structure ParseSyntax : PARSE_ABT
     where type ParseOperator.world = Development.label -> Arity.t

   structure Ctt : CTT_UTIL
     where type label = Development.label
     where type tactic = Development.tactic
     where type world = Development.t
     where type term = ParseSyntax.t
     where type name = ParseSyntax.Variable.t):
sig
  structure Lcf : ANNOTATED_LCF
  type world = Development.t
  val parseRule : world -> Lcf.tactic CharParser.charParser
end =
struct
  structure AnnLcf = Lcf
  structure Tacticals = Tacticals (Lcf)
  open Ctt Lcf Tacticals ParserCombinators CharParser
  structure Lcf = AnnLcf

  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  open JonprlTokenParser Rules

  type world = Development.t

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parseLevel =
    lexeme (symbol "@" >> parseInt)

  val parseIndex =
    lexeme (symbol "#" >> parseInt)

  fun parseOpt p =
    symbol "_" return NONE
      || p wth SOME

  val parseName =
    identifier
      wth ParseSyntax.Variable.named

  fun decorateTac tac =
    fn (name, args) => fn (pos : Pos.t) =>
      Lcf.annotate ({name = name, pos = pos}, tac args)

  fun nameTac name tac =
    fn (pos : Pos.t) =>
      Lcf.annotate ({name = name, pos = pos}, tac)

  type 'a intensional_parser = world -> 'a charParser
  type tactic_parser = (Pos.t -> tactic) intensional_parser

  val parseTm : term intensional_parser =
    squares o ParseSyntax.parseAbt [] o Development.lookupOperator

  val parseCum : tactic_parser =
    fn D => symbol "cum"
      && opt parseLevel
      wth (fn (name, k) => nameTac name (Cum k))

  val parseWitness : tactic_parser =
    fn D => symbol "witness"
      && parseTm D
      wth (fn (name, tm) =>
        nameTac name (Witness tm))

  val parseHypothesis : tactic_parser =
    fn D => symbol "hypothesis"
      && parseIndex
      wth (fn (name, i) =>
        nameTac name (Hypothesis i))

  val parseEqSubst : tactic_parser =
    fn D => symbol "subst"
      && parseTm D && parseTm D && opt parseLevel
      wth (fn (name, (M, (N, k))) =>
        nameTac name (EqSubst (M, N, k)))

  val parseDir =
    (symbol "→" || symbol "->") return RIGHT
      || (symbol "←" || symbol "<-") return LEFT

  val parseHypSubst : tactic_parser =
    fn D => symbol "hyp-subst"
      && parseDir
      && parseIndex
      && parseTm D && opt parseLevel
      wth (fn (name, (dir, (i, (M, k)))) =>
        nameTac name (HypEqSubst (dir, i, M, k)))

  val parseIntroArgs : intro_args intensional_parser =
    fn D => opt (parseTm D)
      && opt (brackets parseName)
      && opt parseLevel
      wth (fn (tm, (z, k)) =>
            {term = tm,
             freshVariable = z,
             level = k})

  val parseNames =
    opt (brackets (commaSep1 parseName))
    wth (fn SOME xs => xs
          | NONE => [])

  val parseElimArgs : elim_args intensional_parser=
    fn D => parseIndex
      && opt (parseTm D)
      && parseNames
      wth (fn (i, (M, names)) =>
            {target = i,
             term = M,
             names = names})

  val parseTerms : term list intensional_parser =
    fn D => opt (squares (commaSep1 (ParseSyntax.parseAbt [] (Development.lookupOperator D))))
    wth (fn oxs => getOpt (oxs, []))

  val parseEqCdArgs : eq_cd_args intensional_parser =
    fn D => (parseTerms D)
      && parseNames
      && opt parseLevel
      wth (fn (Ms, (xs, k)) => {names = xs, terms = Ms, level = k})

  val parseExtArgs : ext_args intensional_parser =
    fn D => opt (brackets parseName)
      && opt parseLevel
      wth (fn (z,k) => {freshVariable = z, level = k})

  val parseIntro =
    fn D => symbol "intro"
      && parseIntroArgs D
      wth (fn (name, args) => nameTac name (Intro args))

  val parseElim =
    fn D => symbol "elim"
      && parseElimArgs D
      wth (fn (name, args) => nameTac name (Elim args))

  val parseEqCd =
    fn D => symbol "eq-cd"
      && (parseEqCdArgs D)
      wth (fn (name, args) => nameTac name (EqCD args))

  val parseExt =
    fn D => symbol "ext"
      && parseExtArgs D
      wth (fn (name, args) => nameTac name (Ext args))

  val parseSymmetry : tactic_parser =
    fn D => symbol "symmetry"
      wth (fn name => nameTac name EqSym)

  val parseAssumption : tactic_parser =
    fn D => symbol "assumption"
      wth (fn name => nameTac name Assumption)

  val parseMemCd : tactic_parser =
    fn D => symbol "mem-cd"
      wth (fn name => nameTac name MemCD)

  val parseAuto : tactic_parser =
    fn D => symbol "auto"
      wth (fn name => nameTac name Auto)

  val parseLemma : tactic_parser =
    fn D => symbol "lemma"
      && brackets identifier
      wth (fn (name, lbl) => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Lemma (D, lbl)))

  val parseUnfold : tactic_parser =
    fn D => symbol "unfold"
      && brackets (separate identifier whiteSpace)
      wth (fn (name, lbls) => fn pos =>
             Lcf.annotate ({name = name, pos = pos}, Unfolds (D, lbls)))

  val parseCustomTactic : tactic_parser =
    fn D => symbol "refine"
      >> brackets identifier
      wth (fn lbl => fn (pos : Pos.t) =>
            Lcf.annotate ({name = lbl, pos = pos}, fn goal =>
              Development.lookupTactic D lbl goal))

  fun tacticParsers D =
    parseLemma D
      || parseUnfold D
      || parseCustomTactic D
      || parseWitness D
      || parseHypothesis D
      || parseEqSubst D
      || parseHypSubst D
      || parseIntro D
      || parseElim D
      || parseEqCd D
      || parseExt D
      || parseCum D
      || parseAuto D
      || parseMemCd D
      || parseAssumption D
      || parseSymmetry D

  val parseRule : Development.t -> tactic charParser =
    fn D => !! (tacticParsers D)
    wth (fn (t, pos) => t pos)

end

structure CttRuleParser = CttRuleParser
  (structure Ctt = CttUtil
   structure Lcf = AnnotatedLcf
   structure Development = Development
   structure ParseSyntax = Syntax)

structure CttScript = TacticScript
  (struct
    structure LcfApart = Lcf
    open CttRuleParser
   end)

