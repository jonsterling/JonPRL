structure Lang =
struct
  datatype t
    = UNIV
    | VOID
    | UNIT | AX | MATCH_UNIT
    | PROD | PAIR | SPREAD
    | FUN | LAM | AP
    | CAN_EQ | EQ
    | MEM

  fun eq (x : t) y = x = y

  fun arity UNIV = #[]
    | arity VOID = #[]
    | arity UNIT = #[]
    | arity AX = #[]
    | arity MATCH_UNIT = #[0,0]
    | arity PROD = #[0,1]
    | arity PAIR = #[0,0]
    | arity SPREAD = #[0,2]
    | arity FUN = #[0,1]
    | arity LAM = #[1]
    | arity AP = #[0,0]
    | arity EQ = #[0,0,0]
    | arity CAN_EQ = #[0,0,0]
    | arity MEM = #[0,0]

  fun to_string UNIV = "univ"
    | to_string VOID = "void"
    | to_string UNIT = "unit"
    | to_string AX = "ax"
    | to_string MATCH_UNIT = "match"
    | to_string PROD = "prod"
    | to_string PAIR = "pair"
    | to_string SPREAD = "spread"
    | to_string FUN = "fun"
    | to_string LAM = "λ"
    | to_string AP = "ap"
    | to_string EQ = "=*"
    | to_string CAN_EQ = "="
    | to_string MEM = "∈"
end
