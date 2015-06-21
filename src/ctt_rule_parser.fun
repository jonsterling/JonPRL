functor CttRuleParser
  (structure Tactic : TACTIC
     where type level = int
   structure ParseSyntax : PARSE_ABT
     where type t = Tactic.term
     where type Variable.t = Tactic.name
     where type ParseOperator.world = Tactic.label -> Arity.t
   type world
   val lookupOperator : world -> Tactic.label -> Arity.t
   val stringToLabel  : string -> Tactic.label):
sig
  val parseRule : world -> Tactic.t CharParser.charParser
end =
struct
  type world = world
  open Tactic ParserCombinators CharParser

  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  open JonprlTokenParser

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

  val parseLabel = identifier wth stringToLabel

  type 'a intensional_parser = world -> 'a charParser
  type tactic_parser = (Pos.t -> Tactic.t) intensional_parser

  val parseTm : ParseSyntax.t intensional_parser =
    squares o ParseSyntax.parseAbt [] o lookupOperator

  val parseCum : tactic_parser =
    fn D => symbol "cum"
      && opt parseLevel
      wth (fn (name, k) => fn pos => CUM (k, {name = name, pos = pos}))

  val parseWitness : tactic_parser =
    fn D => symbol "witness"
      && parseTm D
      wth (fn (name, tm) => fn pos =>
              WITNESS (tm, {name = name, pos = pos}))

  val parseHypothesis : tactic_parser =
    fn D => symbol "hypothesis"
      && parseIndex
      wth (fn (name, i) => fn pos =>
        HYPOTHESIS (i, {name = name, pos = pos}))

  val parseEqSubst : tactic_parser =
    fn D => symbol "subst"
      && parseTm D && parseTm D && opt parseLevel
      wth (fn (name, (M, (N, k))) => fn pos =>
              EQ_SUBST ({left = M, right = N, level = k},
                        {name = name, pos = pos}))

  val parseDir =
    (symbol "→" || symbol "->") return Dir.RIGHT
      || (symbol "←" || symbol "<-") return Dir.LEFT

  val parseHypSubst : tactic_parser =
    fn D => symbol "hyp-subst"
      && parseDir
      && parseIndex
      && parseTm D && opt parseLevel
      wth (fn (name, (dir, (i, (M, k)))) => fn pos =>
              HYP_SUBST ({dir = dir,
                          index = i,
                          domain = M,
                          level = k},
                         {name = name, pos = pos}))

  val parseIntroArgs =
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

  val parseElimArgs =
    fn D => parseIndex
      && opt (parseTm D)
      && parseNames
      wth (fn (i, (M, names)) =>
            {target = i,
             term = M,
             names = names})

  val parseTerms : term list intensional_parser =
    fn D => opt (squares (commaSep1 (ParseSyntax.parseAbt [] (lookupOperator D))))
    wth (fn oxs => getOpt (oxs, []))

  val parseEqCdArgs =
    fn D => (parseTerms D)
      && parseNames
      && opt parseLevel
      wth (fn (Ms, (xs, k)) => {names = xs, terms = Ms, level = k})

  val parseExtArgs =
    fn D => opt (brackets parseName)
      && opt parseLevel
      wth (fn (z,k) => {freshVariable = z, level = k})

  val parseIntro =
    fn D => symbol "intro"
      && parseIntroArgs D
      wth (fn (name, args) => fn pos =>
              INTRO (args, {name = name, pos = pos}))

  val parseElim =
    fn D => symbol "elim"
      && parseElimArgs D
      wth (fn (name, args) => fn pos =>
              ELIM (args, {pos = pos, name = name}))

  val parseEqCd =
    fn D => symbol "eq-cd"
      && (parseEqCdArgs D)
      wth (fn (name, args) => fn pos =>
              EQ_CD (args, {name = name, pos = pos}))

  val parseExt =
    fn D => symbol "ext"
      && parseExtArgs D
      wth (fn (name, args) => fn pos =>
              EXT (args, {name = name, pos = pos}))

  val parseSymmetry : tactic_parser =
    fn D => symbol "symmetry"
      wth (fn name => fn pos => SYMMETRY {name = name, pos = pos})

  val parseAssumption : tactic_parser =
    fn D => symbol "assumption"
      wth (fn name => fn pos => ASSUMPTION {name = name, pos = pos})

  val parseMemCd : tactic_parser =
    fn D => symbol "mem-cd"
      wth (fn name => fn pos => MEM_CD {name = name, pos = pos})

  val parseAuto : tactic_parser =
    fn D => symbol "auto"
      wth (fn name => fn pos => AUTO {name = name, pos = pos})

  val parseLemma : tactic_parser =
    fn D => symbol "lemma"
      && brackets parseLabel
      wth (fn (name, lbl) => fn pos =>
             LEMMA (lbl, {name = name, pos = pos}))

  val parseUnfold : tactic_parser =
    fn D => symbol "unfold"
      && brackets (separate parseLabel whiteSpace)
      wth (fn (name, lbls) => fn pos =>
             UNFOLD (lbls, ({name = name, pos = pos})))

  val parseCustomTactic : tactic_parser =
    fn D => symbol "refine"
      >> brackets identifier
      wth (fn name => fn (pos : Pos.t) =>
            CUSTOM_TACTIC (stringToLabel name, {name = name, pos = pos}))

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

  val parseRule : world -> Tactic.t charParser =
    fn D => !! (tacticParsers D)
    wth (fn (t, pos) => t pos)
end

structure CttRuleParser = CttRuleParser
  (structure Tactic = Tactic
   structure ParseSyntax = Syntax
   type world = Development.world
   val lookupOperator = Development.lookupOperator
   val stringToLabel  = StringVariable.named)

structure CttScript = TacticScript
  (struct
    structure Tactic = Tactic
    open CttRuleParser
    type world = Development.world
   end)
