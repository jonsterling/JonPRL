structure Operator =
struct
  datatype t
    = (* Derivations *)
      UNIV_EQ | CUM
    | VOID_EQ | VOID_ELIM
    | UNIT_EQ | UNIT_INTRO | UNIT_ELIM | AX_EQ
    | PROD_EQ | PROD_INTRO | PROD_ELIM | PAIR_EQ | SPREAD_EQ
    | FUN_EQ | FUN_INTRO | FUN_ELIM | LAM_EQ | AP_EQ
    | ISECT_EQ | ISECT_INTRO | ISECT_MEMBER_EQ
    | WITNESS | HYP_EQ
    | SQUASH_EQ | SQUASH_INTRO | SQUASH_ELIM

    | ADMIT

      (* Computational Type Theory *)
    | UNIV of Level.t
    | VOID
    | UNIT | AX
    | PROD | PAIR | SPREAD
    | FUN | LAM | AP
    | ISECT
    | EQ | MEM
    | SQUASH

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

       | ISECT_EQ => #[0,1]
       | ISECT_INTRO => #[1,0]
       | ISECT_MEMBER_EQ => #[1,0]

       | WITNESS => #[0,0]
       | HYP_EQ => #[0]

       | SQUASH_EQ => #[0]
       | SQUASH_INTRO => #[0]
       | SQUASH_ELIM => #[0]

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

       | SQUASH => #[0]

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

       | ISECT_EQ => "isect="
       | ISECT_INTRO => "isect-intro"
       | ISECT_MEMBER_EQ => "isect-mem="

       | WITNESS => "witness"
       | HYP_EQ => "hyp="
       | ADMIT => "<<<<<ADMIT>>>>>"

       | SQUASH_EQ => "squash="
       | SQUASH_INTRO => "squash-intro"
       | SQUASH_ELIM => "squash-elim"

       | UNIV i => "U<" ^ Level.to_string i ^ ">"
       | VOID => "void"
       | UNIT => "unit"
       | AX => "•"
       | PROD => "prod"
       | PAIR => "pair"
       | SPREAD => "spread"
       | FUN => "∏"
       | LAM => "λ"
       | AP => "ap"
       | ISECT => "∩"
       | EQ => "="
       | MEM => "∈"

       | SQUASH => "↓"
end
