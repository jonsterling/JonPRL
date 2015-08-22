functor TacticParser
  ( structure Tactic : TACTIC
     where type level = Level.t
     where type label = Label.t
   structure ParseSyntax : PARSE_ABT
     where type t = Tactic.term
     where type Variable.t = Tactic.name
     where type ParseOperator.world = ParserContext.world
     where type ParseOperator.t = Tactic.operator
   ) :> INTENSIONAL_PARSER
         where type world = ParserContext.world
           and type t = Tactic.t =
struct
  open ParserContext Tactic ParserCombinators CharParser

  infix 2 return wth suchthat return guard when
  infixr 1 || <|>
  infixr 3 &&
  infixr 4 << >>

  open JonprlTokenParser

  fun tactic s =
    repeat1 JonprlLanguageDef.identLetter << whiteSpace
      wth String.implode
      suchthat (fn s' => s = s')

  val parseInt =
    repeat1 digit wth valOf o Int.fromString o String.implode

  val parseLevel =
    lexeme (symbol "@" >> Level.parse)

  val parseIndex =
    lexeme (symbol "#" >> parseInt)

  val parseName =
    identifier
      wth ParseSyntax.Variable.named

  val parseHyp =
    parseIndex wth HypSyn.INDEX
      || brackets parseName wth HypSyn.NAME

  fun parseOpt p =
    symbol "_" return NONE
      || p wth SOME

  val parseLabel = identifier

  type 'a intensional_parser = world -> 'a charParser
  type tactic_parser = (Pos.t -> Tactic.t) intensional_parser

  fun parseTm w =
    squares (ParseSyntax.parseAbt w (ParseSyntax.initialState []))

  val parseCum : tactic_parser =
    fn w => tactic "cum"
      && opt parseLevel
      wth (fn (name, k) => fn pos => CUM (k, {name = name, pos = pos}))

  val parseWitness : tactic_parser =
    fn w => tactic "witness"
      && parseTm w
      wth (fn (name, tm) => fn pos =>
              WITNESS (tm, {name = name, pos = pos}))

  val parseHypothesis : tactic_parser =
    fn w => tactic "hypothesis"
      && parseHyp
      wth (fn (name, i) => fn pos =>
        HYPOTHESIS (i, {name = name, pos = pos}))

  val parseEqSubst : tactic_parser =
    fn w => tactic "subst"
      && parseTm w && parseTm w && opt parseLevel
      wth (fn (name, (M, (N, k))) => fn pos =>
              EQ_SUBST ({equality = M, domain = N, level = k},
                        {name = name, pos = pos}))

  val parseDir =
    (symbol "→" || symbol "->") return Dir.RIGHT
      || (symbol "←" || symbol "<-") return Dir.LEFT

  val parseReduceEquand : tactic_parser =
    fn w => tactic "reduce-equand"
      && parseDir
      wth (fn (name, dir) => fn pos =>
        REDUCE_EQUAND (dir, {name = name, pos = pos}))

  val parseHypSubst : tactic_parser =
    fn w => tactic "hyp-subst"
      && parseDir
      && parseHyp
      && parseTm w && opt parseLevel
      wth (fn (name, (dir, (i, (M, k)))) => fn pos =>
              HYP_SUBST
                ({dir = dir,
                  index = i,
                  domain = M,
                  level = k},
                 {name = name, pos = pos}))

  val parseCEqSubst : tactic_parser =
    fn w => tactic "csubst"
      && parseTm w && parseTm w
      wth (fn (name, (M, N)) => fn pos =>
              CEQ_SUBST ({equality = M, domain = N},
                         {name = name, pos = pos}))

  val parseCHypSubst : tactic_parser =
    fn w => tactic "chyp-subst"
      && parseDir
      && parseHyp
      && parseTm w
      wth (fn (name, (dir, (i, M))) => fn pos =>
              CHYP_SUBST
                ({dir = dir,
                  index = i,
                  domain = M},
                 {name = name, pos = pos}))

  val parseIntroArgs =
    fn w => opt (parseTm w)
      && opt parseIndex
      && opt (brackets parseName)
      && opt parseLevel
      wth (fn (tm, (rule, (z, k))) =>
            {term = tm,
             rule = rule,
             freshVariable = z,
             level = k})

  val parseNames =
    opt (brackets (commaSep1 parseName))
    wth (fn SOME xs => xs
          | NONE => [])

  val parseElimArgs =
    fn w => parseHyp
      && opt (parseTm w)
      && parseNames
      wth (fn (i, (M, names)) =>
            {target = i,
             term = M,
             names = names})

  val parseTerms : term list intensional_parser =
    fn w => opt (squares (commaSep1 (ParseSyntax.parseAbt w (ParseSyntax.initialState []))))
    wth (fn oxs => getOpt (oxs, []))

  val parseEqCdArgs =
    fn w => (parseTerms w)
      && parseNames
      && opt parseLevel
      wth (fn (Ms, (xs, k)) => {names = xs, terms = Ms, level = k})

  val parseExtArgs =
    fn w => opt (brackets parseName)
      && opt parseLevel
      wth (fn (z,k) => {freshVariable = z, level = k})

  val parseIntro =
    fn w => tactic "intro"
      && parseIntroArgs w
      wth (fn (name, args) => fn pos =>
              INTRO (args, {name = name, pos = pos}))

  val parseElim =
    fn w => tactic "elim"
      && parseElimArgs w
      wth (fn (name, args) => fn pos =>
              ELIM (args, {pos = pos, name = name}))

  val parseEqCd =
    fn w => tactic "eq-cd"
      && (parseEqCdArgs w)
      wth (fn (name, args) => fn pos =>
              EQ_CD (args, {name = name, pos = pos}))

  val parseExt =
    fn w => tactic "ext"
      && parseExtArgs w
      wth (fn (name, args) => fn pos =>
              EXT (args, {name = name, pos = pos}))

  val parseSymmetry : tactic_parser =
    fn w => tactic "symmetry"
      wth (fn name => fn pos => SYMMETRY {name = name, pos = pos})

  val parseCEqualSym : tactic_parser =
    fn w => tactic "csymmetry"
      wth (fn name => fn pos => CEQUAL_SYM {name = name, pos = pos})

  val parseCEqualStep : tactic_parser =
    fn w => tactic "step"
      wth (fn name => fn pos => CEQUAL_STEP {name = name, pos = pos})

  val parseCEqualStruct : tactic_parser =
    fn w => tactic "cstruct"
      wth (fn name => fn pos => CEQUAL_STRUCT {name = name, pos = pos})

  val parseCEqualApprox : tactic_parser =
    fn w => tactic "capprox"
      wth (fn name => fn pos => CEQUAL_APPROX {name = name, pos = pos})

  val parseApproxRefl : tactic_parser =
    fn w => tactic "areflexivity"
      wth (fn name => fn pos => APPROX_REFL {name = name, pos = pos})

  val parseBottomDiverges : tactic_parser =
   fn w => tactic "bot-div"
      && parseHyp
      wth (fn (name, i) => fn pos =>
        BOTTOM_DIVERGES (i, {name = name, pos = pos}))

  val parseAssumeHasValue : tactic_parser =
   fn w => tactic "assume-has-value"
      && opt (brackets parseName)
      && opt parseLevel
      wth (fn (name, (n,k)) => fn pos =>
        ASSUME_HAS_VALUE ({name = n, level = k}, {name = name, pos = pos}))

  val parseEqEqBase : tactic_parser =
   fn w => tactic "eq-eq-base"
      wth (fn name => fn pos =>
        EQ_EQ_BASE {name = name, pos = pos})

  val parseAssumption : tactic_parser =
    fn w => tactic "assumption"
      wth (fn name => fn pos => ASSUMPTION {name = name, pos = pos})

  val parseAssert : tactic_parser =
   fn w => tactic "assert" && parseTm w && opt (brackets parseName)
     wth (fn (name, (term, hyp)) => fn pos =>
             ASSERT ({assertion = term, name = hyp},
                     {name = name, pos = pos}))

  val parseAuto : tactic_parser =
    fn w => tactic "auto" && opt parseInt
      wth (fn (name, oi) => fn pos => AUTO (oi, {name = name, pos = pos}))

  val parseReduce : tactic_parser =
    fn w => tactic "reduce"
      && opt parseInt
      wth (fn (name, n) => fn pos => REDUCE (n, {name = name, pos = pos}))

  val parseLemma : tactic_parser =
    fn w => tactic "lemma"
      && brackets (ParseSyntax.ParseOperator.parseOperator w)
      wth (fn (name, theta) => fn pos =>
             LEMMA (theta, {name = name, pos = pos}))

  val parseBHyp : tactic_parser =
    fn w => tactic "bhyp"
      && parseHyp
      wth (fn (name, hyp) => fn pos =>
             BHYP (hyp, {name = name, pos = pos}))

  val parseCutLemma : tactic_parser =
    fn w => tactic "cut-lemma"
      && brackets (ParseSyntax.ParseOperator.parseOperator w)
      && opt (brackets parseName)
      wth (fn (name, (theta, oz)) => fn pos =>
             CUT_LEMMA (theta, oz, {name = name, pos = pos}))

  val parseUnfold : tactic_parser =
    fn w => tactic "unfold"
      && brackets (separate (ParseSyntax.ParseOperator.parseOperator w && opt parseLevel) whiteSpace)
      wth (fn (name, thetas) => fn pos =>
             UNFOLD (thetas, ({name = name, pos = pos})))

  val parseCustomTactic : tactic_parser =
    fn w => identifier
      wth (fn name => fn (pos : Pos.t) =>
            CUSTOM_TACTIC (name, {name = name, pos = pos}))

  val parseThin : tactic_parser =
    fn w => tactic "thin"
      && parseHyp
      wth (fn (name, hyp) => fn (pos : Pos.t) =>
            THIN (hyp, {name = name, pos = pos}))


  val parseFiat : tactic_parser =
    fn w => tactic "fiat"
      wth (fn name => fn (pos : Pos.t) =>
            FIAT {name = name, pos = pos})

  val parseResource : tactic_parser =
    fn w => tactic "resource" && Resource.parse
     wth (fn (name, r) => fn pos => RESOURCE (r, {name = name, pos = pos}))

  fun tacticParsers w =
    parseLemma w
      || parseBHyp w
      || parseCutLemma w
      || parseUnfold w
      || parseWitness w
      || parseHypothesis w
      || parseEqSubst w
      || parseHypSubst w
      || parseReduceEquand w
      || parseIntro w
      || parseElim w
      || parseEqCd w
      || parseExt w
      || parseCum w
      || parseAuto w
      || parseReduce w
      || parseAssumption w
      || parseAssert w
      || parseSymmetry w
      || parseCEqualSym w
      || parseCEqualStep w
      || parseCEqualStruct w
      || parseCEqSubst w
      || parseCEqualApprox w
      || parseApproxRefl w
      || parseBottomDiverges w
      || parseAssumeHasValue w
      || parseEqEqBase w
      || parseCHypSubst w
      || parseThin w
      || parseFiat w
      || parseResource w
      || parseCustomTactic w

  val parse : world -> Tactic.t charParser =
    fn w => !! (tacticParsers w)
    wth (fn (t, pos) => t pos)
end

structure TacticParser = TacticParser
  (structure Tactic = Tactic
   structure ParseSyntax = Syntax)

structure TacticScript = TacticScript
  (structure Tactic = Tactic
   structure RuleParser = TacticParser
   structure ParseSyntax = Syntax)
