structure UniversalOperator = UniversalOperator (type world = ParserContext.world)

structure CttCalculus =
struct
  type world = ParserContext.world

  datatype t =
      UNIV of Level.t
    | VOID
    | UNIT | AX
    | PROD | PAIR | SPREAD | AND
    | FUN | LAM | AP | IMPLIES | IFF
    | ID | BOT | SQUASH
    | IMAGE
    | FIX
    | CBV
    | ISECT
    | EQ | MEM
    | SUBSET
    | PLUS | INL | INR | DECIDE
    | NAT | ZERO | SUCC | NATREC
    | CEQUAL | APPROX | BASE
    | CUSTOM of {label : Label.t, arity : Arity.t}
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
       ID, BOT, SQUASH,
       IMAGE,
       FIX,
       CBV,
       ISECT, EQ, MEM, SUBSET,
       PLUS, INL, INR, DECIDE,
       NAT, ZERO, SUCC, NATREC,
       CEQUAL, APPROX, BASE, SO_APPLY]
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
       | IMAGE => #[0,0]
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

       | CUSTOM {arity,...} => arity
       | SO_APPLY => #[0,0]

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
       | IMAGE => "image"
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

       | CUSTOM {label,...} => Label.toString label
       | SO_APPLY => "so_apply"

  local
    open ParserCombinators CharParser
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

    val extensionalParseOperator : t charParser =
      choices
        [parseUniv,
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
         string "image" return IMAGE,
         string "fix" return FIX,
         string "cbv" return CBV,
         string "isect" return ISECT,
         string "=" return EQ,
         string "ceq" return CEQUAL,
         string "approx" return APPROX,
         string "member" return MEM,
         string "subset" return SUBSET,
         string "so_apply" return SO_APPLY,
         string "nat" return NAT,
         string "zero" return ZERO,
         string "succ" return SUCC,
         string "natrec" return NATREC]

    fun intensionalParseOperator world =
      JonprlTokenParser.identifier -- (fn lbl =>
        case (SOME (ParserContext.lookupOperator world lbl) handle _ => NONE) of
             SOME (arity, _) => succeed (CUSTOM {label = lbl, arity = arity})
           | NONE => fail "no such operator")

    fun parseOperator lookup =
      intensionalParseOperator lookup
      || extensionalParseOperator
  end
end

structure CttCalculusInj = OperatorInjection
  (structure Operator = CttCalculus
   structure Universe = UniversalOperator.Universe)

