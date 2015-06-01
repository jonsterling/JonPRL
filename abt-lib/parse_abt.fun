functor ParseAbt
  (structure Syntax : ABT_UTIL
   structure Operator : PARSE_OPERATOR
   sharing Syntax.Operator = Operator) : PARSE_ABT =
struct
  structure ParseOp = Operator

  val force = ParserCombinators.$
  open ParserCombinators CharParser Syntax

  infix 5 $$ \\

  infixr 4 << >>
  infixr 3 &&
  infix 2 -- ##
  infix 2 wth suchthat return guard when
  infixr 1 || <|> ??

  structure LangDef :> LANGUAGE_DEF =
  struct
    type scanner = char CharParser.charParser
    val commentStart = NONE
    val commentEnd = NONE
    val commentLine = NONE
    val nestedComments = false

    val identStart =
      CharParser.letter
        || CharParser.oneOf (String.explode "_'ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσΤτΥυΦφΧχΨψΩω")
    val identLetter = identStart || CharParser.digit
    val opStart = fail "Operators not supported" : scanner
    val opLetter = opStart
    val reservedNames = []
    val reservedOpNames = []
    val caseSensitive = true
  end

  structure TP = TokenParser (LangDef)
  open TP

  structure SymbolTable =
  struct
    type table = Variable.t StringListDict.dict
    type t = {bound: table, free: table ref}
    fun bind {bound,free} (n, v) =
      {bound = StringListDict.insert bound n v,
       free = free}

    fun named {bound,free} n =
      StringListDict.lookup bound n
      handle _ => StringListDict.lookup (!free) n
      handle _ =>
        let
          val v = Variable.named n
        in
          free := StringListDict.insert (!free) n v;
          v
        end

    val empty : t =
      {bound = StringListDict.empty,
       free = ref StringListDict.empty}
  end

  fun parens p = (symbol "(" >> spaces) >> p << (spaces >> symbol ")")
  fun >>= (p : 'a charParser, q : 'a -> 'b charParser) : 'b charParser = join (p wth q)
  infix >>=

  local
    val new_variable = identifier wth (fn x => (x, Variable.named x))
    fun var sigma = identifier wth (fn x => `` (SymbolTable.named sigma x))

    fun abt sigma () = force (app sigma) || force (abs sigma) || var sigma ?? "abt"
    and app sigma () =
      ParseOp.parse_operator
        && opt (parens (force (args sigma)))
        wth (fn (O, ES) => O $$ (getOpt (ES, #[]))) ?? "app"
    and abs sigma () =
      (new_variable << spaces << symbol "." << spaces >>= (fn (n,v) =>
        let
          val sigma' = SymbolTable.bind sigma (n,v)
        in
          force (abt sigma') wth (fn E => v \\ E)
        end)) ?? "abs"

    and args sigma () = separate (force (abt sigma)) (symbol ";") wth Vector.fromList ?? "args"

  in
    val parse_abt : t charParser = force (abt SymbolTable.empty)
  end
end
