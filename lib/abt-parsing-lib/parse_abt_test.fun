functor ParseAbtTest () =
struct
  datatype oper = LAM | AX | AP

  structure O : PARSE_OPERATOR =
  struct
    type world = unit
    type t = oper
    val eq = op=
    fun arity LAM = #[1]
      | arity AX = #[]
      | arity AP = #[0,0]
    fun toString LAM = "λ"
      | toString AX = "<>"
      | toString AP = "ap"

    open ParserCombinators CharParser
    infix 2 return
    infixr 1 ||

    fun parseOperator () =
      string "λ" return LAM
        || string "<>" return AX
        || string "ap" return AP
  end

  structure Syn = AbtUtil(Abt(structure Operator = O and Variable = Variable()))
  structure ParseSyn = ParseAbt(structure Syntax = Syn and Operator = O)

  fun printRes pr = print (Sum.sumR (fn b => Syn.toString b ^ "\n") pr)
  fun doit s = printRes (CharParser.parseString (ParseSyn.parseAbt [] ()) s)

  val _ =
    (doit "λ(x.λ(x.ap(x;<>)))";
     doit "ap(λ(x.x);x)";
     doit "ap(ap(x;x);λ(x.x))")
end
