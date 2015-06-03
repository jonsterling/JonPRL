structure Operator =
struct
  datatype t
    = (* Derivations *)
      UNIV_EQ | CUM
    | EQ_EQ
    | VOID_EQ | VOID_ELIM
    | UNIT_EQ | UNIT_INTRO | UNIT_ELIM | AX_EQ
    | PROD_EQ | PROD_INTRO | PROD_ELIM | PAIR_EQ | SPREAD_EQ
    | FUN_EQ | FUN_INTRO | FUN_ELIM | LAM_EQ | AP_EQ
    | ISECT_EQ | ISECT_INTRO | ISECT_ELIM | ISECT_MEMBER_EQ | ISECT_MEMBER_CASE_EQ
    | WITNESS | HYP_EQ | EQ_SUBST | EQ_SYM
    | SUBSET_EQ | SUBSET_INTRO | SUBSET_ELIM | SUBSET_MEMBER_EQ

    | ADMIT

      (* Computational Type Theory *)
    | UNIV of Level.t
    | VOID
    | UNIT | AX
    | PROD | PAIR | SPREAD
    | FUN | LAM | AP
    | ISECT
    | EQ | MEM
    | SUBSET

  val eq = op=

  fun arity O =
    case O of
         UNIV_EQ => #[]
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
       | PROD_ELIM => #[0,2]
       | PAIR_EQ => #[0,0,1]
       | SPREAD_EQ => #[0,3]

       | FUN_EQ => #[0,1]
       | FUN_INTRO => #[1,0]
       | FUN_ELIM => #[0,0,0,2]
       | LAM_EQ => #[1,0]
       | AP_EQ => #[0,0]

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
       | SUBSET_ELIM => #[0,2]
       | SUBSET_MEMBER_EQ => #[0,0,1]

       | ADMIT => #[]


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

       | ISECT => #[0,1]

       | EQ => #[0,0,0]
       | MEM => #[0,0]

       | SUBSET => #[0,1]

  fun to_string O =
    case O of
         UNIV_EQ => "U⁼"
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
       | PROD_ELIM => "prod-elim"
       | PAIR_EQ => "pair⁼"
       | SPREAD_EQ => "spread⁼"

       | FUN_EQ => "fun⁼"
       | FUN_INTRO => "fun-intro"
       | FUN_ELIM => "fun-elim"
       | LAM_EQ => "lam⁼"
       | AP_EQ => "ap⁼"

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

       | SUBSET_EQ => "subset⁼"
       | SUBSET_INTRO => "subset-intro"
       | SUBSET_ELIM => "subset-elim"
       | SUBSET_MEMBER_EQ => "subset-member-eq"

       | UNIV i => "U<" ^ Level.to_string i ^ ">"
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

       | SUBSET => "subset"

  local
    open ParserCombinators CharParser
    infix 2 return wth suchthat return guard when
    infixr 1 ||
    infixr 4 << >>
  in
    val parse_int =
      repeat1 digit wth valOf o Int.fromString o String.implode

    val parse_univ =
      string "U<" >> parse_int << string ">" wth UNIV

    val parse_operator =
      parse_univ
        || string "void" return VOID
        || string "unit" return UNIT
        || string "<>" return AX
        || string "Σ" return PROD
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
  end
end
