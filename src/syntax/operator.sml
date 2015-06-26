structure OperatorType =
struct
  datatype 'label operator =
      (* Derivations *)
      UNIV_EQ of Level.t | CUM
    | EQ_EQ
    | VOID_EQ | VOID_ELIM
    | UNIT_EQ | UNIT_INTRO | UNIT_ELIM | AX_EQ
    | PROD_EQ | PROD_INTRO | IND_PROD_INTRO | PROD_ELIM | PAIR_EQ | SPREAD_EQ
    | FUN_EQ | FUN_INTRO | FUN_ELIM | LAM_EQ | AP_EQ | FUN_EXT
    | ISECT_EQ | ISECT_INTRO | ISECT_ELIM | ISECT_MEMBER_EQ | ISECT_MEMBER_CASE_EQ
    | WITNESS | HYP_EQ | EQ_SUBST | EQ_SYM
    | SUBSET_EQ | SUBSET_INTRO | IND_SUBSET_INTRO | SUBSET_ELIM | SUBSET_MEMBER_EQ
    | PLUS_EQ | PLUS_INTROL | PLUS_INTROR | PLUS_ELIM | INL_EQ | INR_EQ | DECIDE_EQ

    | ADMIT | ASSERT

      (* Computational Type Theory *)
    | UNIV of Level.t
    | VOID
    | UNIT | AX
    | PROD | PAIR | SPREAD
    | FUN | LAM | AP
    | ISECT
    | EQ | MEM
    | SUBSET
    | PLUS | INL | INR | DECIDE

    | CUSTOM of {label : 'label, arity : Arity.t}
    | SO_APPLY
end

signature CTT_OPERATOR =
sig
  structure Label : LABEL

  include PARSE_OPERATOR
    where type t = Label.t OperatorType.operator
    where type world = Label.t -> Arity.t

end

functor Operator (Label : PARSE_LABEL) : CTT_OPERATOR =
struct
  open OperatorType
  structure Label = Label
  type t = Label.t operator

  type world = Label.t -> Arity.t
  fun eq (UNIV_EQ i, UNIV_EQ j) = i = j
    | eq (CUM, CUM) = true
    | eq (EQ_EQ, EQ_EQ) = true
    | eq (VOID_EQ, VOID_EQ) = true
    | eq (VOID_ELIM, VOID_ELIM) = true
    | eq (UNIT_EQ, UNIT_EQ) = true
    | eq (UNIT_INTRO, UNIT_INTRO) = true
    | eq (UNIT_ELIM, UNIT_ELIM) = true
    | eq (AX_EQ, AX_EQ) = true
    | eq (PROD_EQ, PROD_EQ) = true
    | eq (PROD_INTRO, PROD_INTRO) = true
    | eq (IND_PROD_INTRO, IND_PROD_INTRO) = true
    | eq (PROD_ELIM, PROD_ELIM) = true
    | eq (PAIR_EQ, PAIR_EQ) = true
    | eq (SPREAD_EQ, SPREAD_EQ) = true
    | eq (FUN_EQ, FUN_EQ) = true
    | eq (FUN_INTRO, FUN_INTRO) = true
    | eq (FUN_ELIM, FUN_ELIM) = true
    | eq (LAM_EQ, LAM_EQ) = true
    | eq (AP_EQ, AP_EQ) = true
    | eq (FUN_EXT, FUN_EXT) = true
    | eq (ISECT_EQ, ISECT_EQ) = true
    | eq (ISECT_INTRO, ISECT_INTRO) = true
    | eq (ISECT_ELIM, ISECT_ELIM) = true
    | eq (ISECT_MEMBER_EQ, ISECT_MEMBER_EQ) = true
    | eq (ISECT_MEMBER_CASE_EQ, ISECT_MEMBER_CASE_EQ) = true
    | eq (WITNESS, WITNESS) = true
    | eq (SUBSET_EQ, SUBSET_EQ) = true
    | eq (SUBSET_INTRO, SUBSET_INTRO) = true
    | eq (IND_SUBSET_INTRO, IND_SUBSET_INTRO) = true
    | eq (SUBSET_ELIM, SUBSET_ELIM) = true
    | eq (SUBSET_MEMBER_EQ, SUBSET_MEMBER_EQ) = true
    | eq (ADMIT, ADMIT) = true
    | eq (ASSERT, ASSERT) = true
    | eq (UNIV i, UNIV j) = i = j
    | eq (VOID, VOID) = true
    | eq (UNIT, UNIT) = true
    | eq (AX, AX) = true
    | eq (PROD, PROD) = true
    | eq (PAIR, PAIR) = true
    | eq (SPREAD, SPREAD) = true
    | eq (FUN, FUN) = true
    | eq (LAM, LAM) = true
    | eq (AP, AP) = true
    | eq (ISECT, ISECT) = true
    | eq (EQ, EQ) = true
    | eq (MEM, MEM) = true
    | eq (SUBSET, SUBSET) = true
    | eq (CUSTOM o1, CUSTOM o2) = Label.eq (#label o1, #label o2)
    | eq (SO_APPLY,SO_APPLY) = true
    | eq (PLUS_EQ, PLUS_EQ) = true
    | eq (PLUS_INTROL, PLUS_INTROL) = true
    | eq (PLUS_INTROR, PLUS_INTROR) = true
    | eq (PLUS_ELIM, PLUS_ELIM) = true
    | eq (INL_EQ, INL_EQ) = true
    | eq (INR_EQ, INR_EQ) = true
    | eq (DECIDE_EQ, DECIDE_EQ) = true
    | eq (PLUS, PLUS) = true
    | eq (INL, INL) = true
    | eq (INR, INR) = true
    | eq (DECIDE, DECIDE) = true
    | eq _ = false

  fun arity O =
    case O of
         UNIV_EQ _ => #[]
       | CUM => #[0]
       | EQ_EQ => #[0,0,0]
       | VOID_EQ => #[]
       | VOID_ELIM => #[0]

       | UNIT_EQ => #[]
       | UNIT_INTRO => #[]
       | UNIT_ELIM => #[0,0]
       | AX_EQ => #[]

       | PROD_EQ => #[0,1]
       | PROD_INTRO => #[0,0,0,1]
       | IND_PROD_INTRO => #[0,0]
       | PROD_ELIM => #[0,2]
       | PAIR_EQ => #[0,0,1]
       | SPREAD_EQ => #[0,3]

       | PLUS_EQ => #[0, 0]
       | PLUS_INTROL => #[0, 0] (* The extra arg is that the other *)
       | PLUS_INTROR => #[0, 0] (* branch has a type. Just a wf-ness goal *)
       | PLUS_ELIM => #[0, 1, 1]
       | INL_EQ => #[0, 0]
       | INR_EQ => #[0, 0]
       | DECIDE_EQ => #[0, 2, 2]

       | FUN_EQ => #[0,1]
       | FUN_INTRO => #[1,0]
       | FUN_ELIM => #[0,0,0,2]
       | LAM_EQ => #[1,0]
       | AP_EQ => #[0,0]
       | FUN_EXT => #[1,0,0,0]

       | ISECT_EQ => #[0,1]
       | ISECT_INTRO => #[1,0]
       | ISECT_ELIM => #[0,0,0,2]
       | ISECT_MEMBER_EQ => #[1,0]
       | ISECT_MEMBER_CASE_EQ => #[0,0]

       | WITNESS => #[0,0]
       | HYP_EQ => #[0]
       | EQ_SUBST => #[0,0,1]
       | EQ_SYM => #[0]

       | SUBSET_EQ => #[0,1]
       | SUBSET_INTRO => #[0,0,0,1]
       | IND_SUBSET_INTRO => #[0,0]
       | SUBSET_ELIM => #[0,2]
       | SUBSET_MEMBER_EQ => #[0,0,1]

       | ADMIT => #[]
       | ASSERT => #[0, 1]

       | UNIV i => #[]
       | VOID => #[]
       | UNIT => #[]
       | AX => #[]
       | PROD => #[0,1]
       | PAIR => #[0,0]
       | SPREAD => #[0,2]
       | FUN => #[0,1]
       | LAM => #[1]
       | AP => #[0,0]
       | PLUS => #[0, 0]
       | INL => #[0]
       | INR => #[0]
       | DECIDE => #[0, 1, 1]

       | ISECT => #[0,1]

       | EQ => #[0,0,0]
       | MEM => #[0,0]

       | SUBSET => #[0,1]

       | CUSTOM {arity,...} => arity
       | SO_APPLY => #[0,0]

  fun toString O =
    case O of
         UNIV_EQ i => "U⁼{" ^ Level.toString i ^ "}"
       | CUM => "cum"
       | VOID_EQ => "void⁼"
       | VOID_ELIM => "void-elim"

       | EQ_EQ => "eq⁼"
       | UNIT_EQ => "unit⁼"
       | UNIT_INTRO => "unit-intro"
       | UNIT_ELIM => "unit-elim"
       | AX_EQ => "⬧⁼"

       | PROD_EQ => "prod⁼"
       | PROD_INTRO => "prod-intro"
       | IND_PROD_INTRO => "independent-prod-intro"
       | PROD_ELIM => "prod-elim"
       | PAIR_EQ => "pair⁼"
       | SPREAD_EQ => "spread⁼"

       | FUN_EQ => "fun⁼"
       | FUN_INTRO => "fun-intro"
       | FUN_ELIM => "fun-elim"
       | LAM_EQ => "lam⁼"
       | AP_EQ => "ap⁼"
       | FUN_EXT => "funext"

       | PLUS_INTROL => "plus-introl"
       | PLUS_INTROR => "plus-intror"
       | PLUS_ELIM => "plus-elim"
       | PLUS_EQ => "plus⁼"
       | INL_EQ => "inl-eq"
       | INR_EQ => "inr-eq"
       | DECIDE_EQ => "decide-eq"

       | ISECT_EQ => "isect⁼"
       | ISECT_INTRO => "isect-intro"
       | ISECT_ELIM => "isect-elim"
       | ISECT_MEMBER_EQ => "isect-mem⁼"
       | ISECT_MEMBER_CASE_EQ => "isect-mem-case⁼"

       | WITNESS => "witness"
       | HYP_EQ => "hyp⁼"
       | EQ_SUBST => "subst"
       | EQ_SYM => "sym"
       | ADMIT => "<<<<<ADMIT>>>>>"
       | ASSERT => "assert"

       | SUBSET_EQ => "subset⁼"
       | SUBSET_INTRO => "subset-intro"
       | IND_SUBSET_INTRO => "independent-subset-intro"
       | SUBSET_ELIM => "subset-elim"
       | SUBSET_MEMBER_EQ => "subset-member-eq"

       | UNIV i => "U{" ^ Level.toString i ^ "}"
       | VOID => "void"
       | UNIT => "unit"
       | AX => "⬧"
       | PROD => "Σ"
       | PAIR => "pair"
       | SPREAD => "spread"
       | FUN => "Π"
       | LAM => "λ"
       | AP => "ap"
       | ISECT => "⋂"
       | EQ => "="
       | MEM => "∈"
       | PLUS => "+"
       | INL => "inl"
       | INR => "inr"
       | DECIDE => "decide"

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

    fun angles p =
      middle (string "<") p (string ">")
        || middle (string "〈") p  (string "〉")

    val parseUniv : t charParser =
      string "U" >> middle (string "{") Level.parse (string "}") wth UNIV

    val extensionalParseOperator : t charParser =
      parseUniv
        || string "void" return VOID
        || string "unit" return UNIT
        || string "<>" return AX
        || string "Σ" return PROD
        || string "+" return PLUS
        || string "inl" return INL
        || string "inr" return INR
        || string "decide" return DECIDE
        || string "pair" return PAIR
        || string "spread" return SPREAD
        || string "Π" return FUN
        || string "λ" return LAM
        || string "ap" return AP
        || string "∀" return ISECT
        || string "⋂" return ISECT
        || string "=" return EQ
        || string "∈" return MEM
        || string "subset" return SUBSET
        || string "so_apply" return SO_APPLY

    fun intensionalParseOperator lookup =
      Label.parseLabel -- (fn lbl =>
        case (SOME (lookup lbl) handle _ => NONE) of
             SOME arity => succeed (CUSTOM {label = lbl, arity = arity})
           | NONE => fail "no such operator")

    fun parseOperator lookup =
      intensionalParseOperator lookup
        || extensionalParseOperator
  end
end
