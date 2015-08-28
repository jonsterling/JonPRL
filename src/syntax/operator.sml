structure CttCalculus =
struct
  type world = ParserContext.world
  type operator = UniversalOperator.t

  datatype t =
      UNIV of Level.t
    | VOID
    | UNIT | AX
    | PROD | PAIR | SPREAD | AND
    | FUN | LAM | AP | IMPLIES | IFF
    | ID | BOT | SQUASH | FST | SND | NOT
    | SUBTYPE_REL | BUNION | HASVALUE
    | IMAGE
    | PER
    | FIX
    | CBV
    | ISECT
    | EQ | MEM
    | SUBSET
    | PLUS | INL | INR | DECIDE
    | NAT | ZERO | SUCC | NATREC
    | CEQUAL | APPROX | BASE
    | ATOM | TOKEN of string | MATCH_TOKEN of string vector | TEST_ATOM
    | CONTAINER | MAKE_CONTAINER | SHAPE | REFINEMENT | WTREE | SUP | WTREE_REC
    | SO_APPLY

  local
    val i = Level.base
    val i' = Level.succ i
    val i'' = Level.succ i'
    val i''' = Level.succ i''
    val i'''' = Level.succ i'''
  in
    val publicOperators =
      [UNIV i, UNIV i', UNIV i'', UNIV i''', UNIV i'''',
       VOID, UNIT, AX,
       PROD, PAIR, SPREAD, AND,
       FUN, LAM, AP, IMPLIES, IFF,
       ID, BOT, SQUASH, FST, SND, NOT,
       SUBTYPE_REL, BUNION, HASVALUE,
       IMAGE,
       PER,
       FIX,
       CBV,
       ISECT, EQ, MEM, SUBSET,
       PLUS, INL, INR, DECIDE,
       NAT, ZERO, SUCC, NATREC,
       ATOM, TOKEN "token",
       CEQUAL, APPROX, BASE,
       CONTAINER, MAKE_CONTAINER, SHAPE, REFINEMENT, WTREE, SUP, WTREE_REC,
       SO_APPLY]
  end

  val eq : t * t -> bool = op=

  fun arity theta =
    case theta of
         UNIV i => #[]
       | BASE => #[]
       | VOID => #[]
       | UNIT => #[]
       | AX => #[]
       | PROD => #[0,1]
       | PAIR => #[0,0]
       | SPREAD => #[0,2]
       | AND => #[0,0]
       | FUN => #[0,1]
       | LAM => #[1]
       | AP => #[0,0]
       | IMPLIES => #[0,0]
       | IFF => #[0,0]
       | ID => #[]
       | BOT => #[]
       | SQUASH => #[0]
       | FST => #[0]
       | SND => #[0]
       | NOT => #[0]
       | SUBTYPE_REL => #[0,0]
       | BUNION => #[0,0]
       | HASVALUE => #[0]
       | IMAGE => #[0,0]
       | PER => #[0]
       | FIX => #[0]
       | CBV => #[0, 1]
       | PLUS => #[0, 0]
       | INL => #[0]
       | INR => #[0]
       | DECIDE => #[0, 1, 1]
       | NAT => #[]
       | ZERO => #[]
       | SUCC => #[0]
       | NATREC => #[0,0,2]

       | ISECT => #[0,1]

       | EQ => #[0,0,0]
       | CEQUAL => #[0, 0]
       | APPROX => #[0, 0]
       | MEM => #[0,0]

       | SUBSET => #[0,1]

       | ATOM => #[]
       | TOKEN _ => #[]
       | MATCH_TOKEN toks => Vector.tabulate (Vector.length toks + 2, fn _ => 0)
       | TEST_ATOM => #[0,0,0,0]
       | SO_APPLY => #[0,0]

       | CONTAINER => #[]
       | WTREE => #[0]
       | SUP => #[0,1]
       | WTREE_REC => #[0,3]
       | MAKE_CONTAINER => #[0,1]
       | SHAPE => #[0]
       | REFINEMENT => #[0,0]

  fun toString theta =
    case theta of
         UNIV i => "U{" ^ Level.toString i ^ "}"
       | BASE => "base"
       | VOID => "void"
       | UNIT => "unit"
       | AX => "<>"
       | PROD => "prod"
       | PAIR => "pair"
       | SPREAD => "spread"
       | AND => "and"
       | FUN => "fun"
       | LAM => "lam"
       | AP => "ap"
       | IMPLIES => "implies"
       | IFF => "iff"
       | ID => "id"
       | BOT => "bot"
       | SQUASH => "squash"
       | FST => "fst"
       | SND => "snd"
       | NOT => "not"
       | SUBTYPE_REL => "subtype_rel"
       | BUNION => "bunion"
       | HASVALUE => "has-value"
       | IMAGE => "image"
       | PER => "per"
       | FIX => "fix"
       | CBV => "cbv"
       | ISECT => "isect"
       | EQ => "="
       | CEQUAL => "ceq"
       | APPROX => "approx"
       | MEM => "member"
       | PLUS => "plus"
       | INL => "inl"
       | INR => "inr"
       | DECIDE => "decide"
       | NAT => "nat"
       | ZERO => "zero"
       | SUCC => "succ"
       | NATREC => "natrec"
       | SUBSET => "subset"
       | ATOM => "atom"
       | TOKEN tok => "\"" ^ tok ^ "\""
       | MATCH_TOKEN toks =>
           let
             val n = Vector.length toks
             val toks' = Vector.map (fn x => "\"" ^ x ^ "\"") toks
           in
             "match_token{"
             ^ Vector.foldri (fn (i, s1, s2) => if i = n - 1 then s1 else s1 ^ "; " ^ s2) "" toks'
             ^ "}"
           end
       | TEST_ATOM => "test_atom"
       | CONTAINER => "container"
       | MAKE_CONTAINER => "make-container"
       | SHAPE => "shape"
       | REFINEMENT => "refinement"
       | WTREE => "wtree"
       | WTREE_REC => "wtree-rec"
       | SUP => "sup"
       | SO_APPLY => "so_apply"
end

structure CttCalculusInj = OperatorInjection (CttCalculus)

structure ParseCttOperator =
struct
  open CttCalculus
  local
    open ParserCombinators CharParser JonprlTokenParser
    infix 2 return wth suchthat return guard when
    infixr 1 || <|>
    infixr 4 << >> --
  in
    val parseInt =
      repeat1 digit wth valOf o Int.fromString o String.implode

    fun braces p = middle (string "{") p (string "}")

    val parseUniv : t charParser =
      string "U"
        >> braces Level.parse
        wth UNIV

    fun choices xs =
      foldl (fn (p, p') => p || try p') (fail "unknown operator") xs

    val parseToken : t charParser =
      stringLiteral wth TOKEN

    val parseOperator : t charParser =
      choices
        [parseUniv,
         parseToken,
         string "atom" return ATOM,
         string "base" return BASE,
         string "void" return VOID,
         string "unit" return UNIT,
         string "<>" return AX,
         string "prod" return PROD,
         string "plus" return PLUS,
         string "inl" return INL,
         string "inr" return INR,
         string "decide" return DECIDE,
         string "pair" return PAIR,
         string "spread" return SPREAD,
         string "and" return AND,
         string "fun" return FUN,
         string "lam" return LAM,
         string "ap" return AP,
         string "implies" return IMPLIES,
         string "iff" return IFF,
         string "id" return ID,
         string "bot" return BOT,
         string "squash" return SQUASH,
         string "fst" return FST,
         string "snd" return SND,
         string "not" return NOT,
         string "subtype_rel" return SUBTYPE_REL,
         string "bunion" return BUNION,
         string "has-value" return HASVALUE,
         string "image" return IMAGE,
         string "per" return PER,
         string "fix" return FIX,
         string "cbv" return CBV,
         string "isect" return ISECT,
         string "=" return EQ,
         string "ceq" return CEQUAL,
         string "approx" return APPROX,
         string "member" return MEM,
         string "subset" return SUBSET,
         string "so_apply" return SO_APPLY,
         string "test_atom" return TEST_ATOM,
         string "nat" return NAT,
         string "zero" return ZERO,
         string "succ" return SUCC,
         string "natrec" return NATREC,
         string "container" return CONTAINER,
         string "make-container" return MAKE_CONTAINER,
         string "shape" return SHAPE,
         string "refinement" return REFINEMENT,
         string "wtree" return WTREE,
         string "wtree-rec" return WTREE_REC,
         string "sup" return SUP]
  end
end

structure ParseOperator : PARSE_OPERATOR =
struct
  type world = ParserContext.world
  open UniversalOperator

  open ParserCombinators
  infixr 1 || <|>
  infixr 4 << >> --
  infix 2 wth

  fun intensionalParseOperator world =
    JonprlTokenParser.identifier -- (fn lbl =>
      succeed (#1 (ParserContext.lookupOperator world lbl))
        handle _ => fail "no such operator")

  fun parseOperator world =
    intensionalParseOperator world
    || ParseCttOperator.parseOperator wth CttCalculusInj.`>
end
