structure Lang =
struct
  datatype t
    = UNIV
    | VOID
    | UNIT | AX
    | PROD | PAIR | FST | SND
    | IMP | LAM | AP
    | CAN_EQ | EQ
    | MEM

  fun eq (x : t) y = x = y

  fun arity UNIV = #[]
    | arity VOID = #[]
    | arity UNIT = #[]
    | arity AX = #[]
    | arity PROD = #[0,0]
    | arity PAIR = #[0,0]
    | arity FST = #[0]
    | arity SND = #[0]
    | arity IMP = #[0,0]
    | arity LAM = #[1]
    | arity AP = #[0,0]
    | arity EQ = #[0,0,0]
    | arity CAN_EQ = #[0,0,0]
    | arity MEM = #[0,0]

  fun to_string UNIV = "univ"
    | to_string VOID = "void"
    | to_string UNIT = "unit"
    | to_string AX = "ax"
    | to_string PROD = "prod"
    | to_string PAIR = "pair"
    | to_string FST = "fst"
    | to_string SND = "fst"
    | to_string IMP = "imp"
    | to_string LAM = "λ"
    | to_string AP = "ap"
    | to_string EQ = "=*"
    | to_string CAN_EQ = "="
    | to_string MEM = "∈"
end
