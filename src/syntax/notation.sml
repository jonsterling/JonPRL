structure Notation : NOTATION =
struct
  datatype t =
      INFIX of string * ParserCombinators.associativity * int
    | PREFIX of string * int
    | POSTFIX of string * int

  structure Associativity =
  struct
    open ParserCombinators
    fun toString Left = SOME "<-"
      | toString Right = SOME "->"
      | toString _ = NONE

    open JonprlLanguageDef JonprlTokenParser
    infix 2 return wth suchthat return guard when
    infixr 1 || <|>

    val parse =
      symbol "<-" return Left
      || symbol "->" return Right
      || succeed Non
  end

  fun quoteString str = "\"" ^ str ^ "\""

  fun toString (INFIX (str, assoc, i)) =
        "Infix "
          ^ (case Associativity.toString assoc of
                  SOME assoc => assoc ^ " "
                | NONE => "")
          ^ Int.toString i
          ^ " " ^ quoteString str
    | toString (PREFIX (str, i)) =
        "Prefix " ^ Int.toString i ^ " " ^ quoteString str
    | toString (POSTFIX (str, i)) =
        "Prefix " ^ Int.toString i ^ " " ^ quoteString str

  local
    open ParserCombinators JonprlLanguageDef CharParser
    structure TP = TokenParser
      (open JonprlLanguageDef
       val reservedNames = ["Infix", "Prefix", "Postfix"])
    open TP

    infix 2 return wth suchthat return guard when
    infixr 1 || <|>
    infixr 3 &&
    infixr 4 << >> --

    val parseInt =
      lexeme (repeat1 digit wth valOf o Int.fromString o String.implode)
  in
    val parseInfix =
      reserved "Infix" >>
        Associativity.parse && parseInt && stringLiteral
        wth (fn (assoc, (i, str)) => INFIX (str, assoc, i))

    val parsePrefix =
      reserved "Prefix" >>
        parseInt && stringLiteral
          wth (fn (i, str) => PREFIX (str, i))

    val parsePostfix =
      reserved "Postfix" >>
        parseInt && stringLiteral
          wth (fn (i, str) => POSTFIX (str, i))

    val parse = parseInfix || parsePrefix || parsePostfix
  end
end
