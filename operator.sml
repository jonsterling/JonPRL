structure Operator =
struct
  datatype t
    = (* Derivations *)
      VOID_EQ | VOID_ELIM
    | UNIT_EQ | UNIT_INTRO | UNIT_ELIM | AX_EQ
    | PROD_EQ | PROD_INTRO | PROD_ELIM | PAIR_EQ
    | FUN_EQ | FUN_INTRO | LAM_EQ
    | WITNESS | HYP_EQ

      (* Computational Type Theory *)
    | UNIV
    | VOID
    | UNIT | AX | MATCH_UNIT
    | PROD | PAIR | SPREAD
    | FUN | LAM | AP
    | EQ | MEM

  fun eq O1 (O2 : t) = O1 = O2

  exception Hole

  fun arity O =
    case O of
         VOID_EQ => #[]
       | VOID_ELIM => #[0]

       | UNIT_EQ => #[]
       | UNIT_INTRO => #[]
       | UNIT_ELIM => #[0,0]
       | AX_EQ => #[]

       | PROD_EQ => #[0,1]
       | PROD_INTRO => #[0,0,0]
       | PROD_ELIM => #[0,2]
       | PAIR_EQ => #[0,0,1]

       | FUN_EQ => #[0,1]
       | FUN_INTRO => #[1,0]
       | LAM_EQ => #[1,0]

       | WITNESS => #[0,0]
       | HYP_EQ => #[0]

       | UNIV => #[]
       | VOID => #[]
       | UNIT => #[]
       | AX => #[]
       | MATCH_UNIT => #[0,0]
       | PROD => #[0,1]
       | PAIR => #[0,0]
       | SPREAD => #[0,2]
       | FUN => #[0,1]
       | LAM => #[1]
       | AP => #[0,0]
       | EQ => #[0,0,0]
       | MEM => #[0,0]

  fun to_string O =
    case O of
         VOID_EQ => "void="
       | VOID_ELIM => "void-elim"

       | UNIT_EQ => "unit="
       | UNIT_INTRO => "unit-intro"
       | UNIT_ELIM => "unit-elim"
       | AX_EQ => "ax="

       | PROD_EQ => "prod="
       | PROD_INTRO => "prod-intro"
       | PROD_ELIM => "prod-elim"
       | PAIR_EQ => "pair="

       | FUN_EQ => "fun="
       | FUN_INTRO => "fun-intro"
       | LAM_EQ => "lam="

       | WITNESS => "witness"
       | HYP_EQ => "hyp="

       | UNIV => "𝕌"
       | VOID => "void"
       | UNIT => "unit"
       | AX => "•"
       | MATCH_UNIT => "match"
       | PROD => "prod"
       | PAIR => "pair"
       | SPREAD => "spread"
       | FUN => "∏"
       | LAM => "λ"
       | AP => "ap"
       | EQ => "="
       | MEM => "∈"
end
