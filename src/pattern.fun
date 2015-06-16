structure PatternOperatorType =
struct
  datatype 'label operator = APP of 'label * Arity.t
end

functor PatternOperator
  (structure Label : LABEL
   val parseLabel : Label.t CharParser.charParser) : PARSE_OPERATOR =
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
    exception Hole
    open ParserCombinators CharParser
    infix 2 return wth suchthat return guard when
    infixr 1 || <|>
    infixr 4 << >> --
  in
    fun parseApp lookup =
      parseLabel -- (fn lbl =>
        case (SOME (lookup lbl) handle _ => NONE) of
             SOME arity => succeed (APP (lbl, arity))
           | NONE => fail "no such operator")

    val parseOperator = parseApp
  end
end

structure PatternSyntax : PARSE_ABT =
struct
  structure V =
  struct
    structure Label = StringVariable

    local
      open ParserCombinators CharParser
      infix 2 return wth suchthat return guard when
      infixr 1 ||
      infixr 4 << >>

      structure LangDef :> LANGUAGE_DEF =
      struct
        type scanner = char CharParser.charParser
        val commentStart = SOME "(*"
        val commentEnd = SOME "*)"
        val commentLine = SOME "|||"
        val nestedComments = false

        val identLetter = CharParser.letter || CharParser.oneOf (String.explode "-'_ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσΤτΥυΦφΧχΨψΩω") || CharParser.digit
        val identStart = identLetter
        val opStart = fail "Operators not supported" : scanner
        val opLetter = opStart
        val reservedNames = []
        val reservedOpNames = []
        val caseSensitive = true
      end

      structure TP = TokenParser (LangDef)
      open TP
    in
      val parseLabel : Label.t CharParser.charParser = identifier
    end
  end

  structure PatternOperator = PatternOperator (V)
  structure Abt = Abt
    (structure Operator = PatternOperator
     structure Variable = Syntax.Variable)
  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = PatternOperator)

  open ParseAbt
end


