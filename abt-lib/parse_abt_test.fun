functor ParseAbtTest () =
struct
  datatype oper = LAM | AX | AP

  structure O : PARSE_OPERATOR =
  struct
    type t = oper
    fun eq x (y : oper) = x = y
    fun arity LAM = #[1]
      | arity AX = #[]
      | arity AP = #[0,0]
    fun to_string LAM = "λ"
      | to_string AX = "<>"
      | to_string AP = "ap"

    open ParserCombinators CharParser
    infix 2 return
    infixr 1 ||

    val parse_operator =
      string "λ" return LAM
        || string "<>" return AX
        || string "ap" return AP
  end

  structure Syn = AbtUtil(Abt(structure Operator = O and Variable = Variable()))
  structure ParseSyn = ParseAbt(structure Syntax = Syn and Operator = O)

  fun print_res pr = print (Sum.sumR (fn b => Syn.to_string PrintMode.Debug b ^ "\n") pr)
  fun doit s = print_res (CharParser.parseString ParseSyn.parse_abt s)

  val _ =
    (doit "λ(x.λ(x.ap(x;<>)))";
     doit "ap(λ(x.x);x)")
end

structure T  = ParseAbtTest ()
