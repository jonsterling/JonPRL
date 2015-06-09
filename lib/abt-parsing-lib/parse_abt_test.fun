functor ParseAbtTest () =
struct
  datatype oper = LAM | AX | AP

  structure O : PARSE_OPERATOR =
  struct
    type env = unit
    type t = oper
    val eq = op=
    fun arity LAM = #[1]
      | arity AX = #[]
      | arity AP = #[0,0]
    fun to_string LAM = "λ"
      | to_string AX = "<>"
      | to_string AP = "ap"

    open ParserCombinators CharParser
    infix 2 return
    infixr 1 ||

    fun parse_operator () =
      string "λ" return LAM
        || string "<>" return AX
        || string "ap" return AP
  end

  structure Syn = AbtUtil(Abt(structure Operator = O and Variable = Variable()))
  structure ParseSyn = ParseAbt(structure Syntax = Syn and Operator = O)

  fun print_res pr = print (Sum.sumR (fn b => Syn.to_string b ^ "\n") pr)
  fun doit s = print_res (CharParser.parseString (ParseSyn.parse_abt ()) s)

  val _ =
    (doit "λ(x.λ(x.ap(x;<>)))";
     doit "ap(λ(x.x);x)";
     doit "ap(ap(x;x);λ(x.x))")
end
