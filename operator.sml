structure Operator =
struct
  datatype t
    = (* Derivations *)
      UNIV_EQ | CUM
    | VOID_EQ | VOID_ELIM
    | UNIT_EQ | UNIT_INTRO | UNIT_ELIM | AX_EQ
    | PROD_EQ | PROD_INTRO | PROD_ELIM | PAIR_EQ | SPREAD_EQ
    | FUN_EQ | FUN_INTRO | FUN_ELIM | LAM_EQ | AP_EQ
    | WITNESS | HYP_EQ

      (* Level expressions *)
    | LSUCC

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
         UNIV_EQ => #[]
       | CUM => #[0]
       | VOID_EQ => #[]
       | VOID_ELIM => #[0]

       | UNIT_EQ => #[]
       | UNIT_INTRO => #[]
       | UNIT_ELIM => #[0,0]
       | AX_EQ => #[]

       | PROD_EQ => #[0,1]
       | PROD_INTRO => #[0,0,0]
       | PROD_ELIM => #[0,2]
       | PAIR_EQ => #[0,0,1]
       | SPREAD_EQ => #[0,3]

       | FUN_EQ => #[0,1]
       | FUN_INTRO => #[1,0]
       | FUN_ELIM => #[0,0,0,2]
       | LAM_EQ => #[1,0]
       | AP_EQ => #[0,0]

       | WITNESS => #[0,0]
       | HYP_EQ => #[0]


       | LSUCC => #[0]

       | UNIV => #[0]
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
         UNIV_EQ => "univ="
       | CUM => "cum"
       | VOID_EQ => "void="
       | VOID_ELIM => "void-elim"

       | UNIT_EQ => "unit="
       | UNIT_INTRO => "unit-intro"
       | UNIT_ELIM => "unit-elim"
       | AX_EQ => "ax="

       | PROD_EQ => "prod="
       | PROD_INTRO => "prod-intro"
       | PROD_ELIM => "prod-elim"
       | PAIR_EQ => "pair="
       | SPREAD_EQ => "spread="

       | FUN_EQ => "fun="
       | FUN_INTRO => "fun-intro"
       | FUN_ELIM => "fun-elim"
       | LAM_EQ => "lam="
       | AP_EQ => "ap="

       | WITNESS => "witness"
       | HYP_EQ => "hyp="

       | LSUCC => "s"

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
