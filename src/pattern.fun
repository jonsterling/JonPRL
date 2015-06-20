structure PatternOperatorType =
struct
  datatype 'label operator = APP of 'label * Arity.t
end

functor PatternOperator (Label : PARSE_LABEL) : PARSE_OPERATOR =
struct
  open PatternOperatorType
  type t = Label.t operator
  type env = Label.t -> Arity.t

  fun eq (APP (l,n), APP (l', n')) = Label.eq (l, l')

  local
    fun replicate n x =
      let
        fun go 0 R = R
          | go i R = x :: go (i - 1) R
      in
        go n []
      end
  in
    fun arity (APP (_, ar)) = Vector.fromList (replicate (Vector.length ar) 0)
  end

  fun toString (APP (l, _)) = Label.toString l

  local
    open ParserCombinators CharParser
    infix 2 return wth suchthat return guard when
    infixr 1 || <|>
    infixr 4 << >> --
  in
    fun parseApp lookup =
      Label.parseLabel -- (fn lbl =>
        case (SOME (lookup lbl) handle _ => NONE) of
             SOME arity => succeed (APP (lbl, arity))
           | NONE => fail "no such operator")

    val parseOperator = parseApp
  end
end

structure PatternSyntax : PARSE_ABT =
struct
  structure PatternOperator = PatternOperator (ParseLabel (StringVariable))
  structure Abt = Abt
    (structure Operator = PatternOperator
     structure Variable = Syntax.Variable)
  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = PatternOperator)

  open ParseAbt
end


