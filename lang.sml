structure Lang =
struct
  datatype t
    = VOID
    | UNIT
    | PROD
    | IMP
    | AX
    | PAIR
    | FST
    | SND
    | LAM
    | AP
    | CAN_MEM
    | MEM

  fun eq (x : t) y = x = y

  fun arity VOID = #[]
    | arity UNIT = #[]
    | arity PROD = #[0,0]
    | arity IMP = #[0,0]
    | arity AX = #[]
    | arity PAIR = #[0,0]
    | arity FST = #[0]
    | arity SND = #[0]
    | arity LAM = #[1]
    | arity AP = #[0,0]
    | arity CAN_MEM = #[0,0]
    | arity MEM = #[0,0]

  fun to_string VOID = "void"
    | to_string UNIT = "unit"
    | to_string PROD = "prod"
    | to_string IMP = "imp"
    | to_string AX = "ax"
    | to_string PAIR = "pair"
    | to_string FST = "fst"
    | to_string SND = "fst"
    | to_string LAM = "λ"
    | to_string AP = "ap"
    | to_string CAN_MEM = "∈"
    | to_string MEM = "∈*"
end
