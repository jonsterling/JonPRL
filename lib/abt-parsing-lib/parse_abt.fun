functor ParseAbt
  (structure Syntax : ABT_UTIL
   structure Operator : PARSE_OPERATOR
   sharing Syntax.Operator = Operator) : PARSE_ABT =
struct
  structure ParseOperator = Operator
  type env = Operator.env

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

    val identLetter =
      CharParser.letter
        || CharParser.oneOf (String.explode "_'ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσΤτΥυΦφΧχΨψΩω")
    val identStart = identLetter
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

    fun dict_from_fvs fvs =
      let
        fun go [] R = R
          | go (x::xs) R = go xs (StringListDict.insert R (Variable.to_string x) x)
      in
        go fvs StringListDict.empty
      end

    fun empty fvs : t =
      {bound = StringListDict.empty,
       free = ref (dict_from_fvs fvs)}
  end

  fun parens p = (symbol "(" >> spaces) >> p << (spaces >> symbol ")")
  fun >>= (p : 'a charParser, q : 'a -> 'b charParser) : 'b charParser = join (p wth q)
  infix >>=

  local
    val new_variable = identifier wth (fn x => (x, Variable.named x))
    fun var sigma = identifier wth (fn x => `` (SymbolTable.named sigma x))

    fun abt sigma env () =
      (force (app sigma env)
      || force (abs sigma env)
      || var sigma) ?? "abt"
    and app sigma env () =
      ParseOperator.parse_operator env
        && opt (parens (force (args sigma env)))
        wth (fn (O, ES) => O $$ getOpt (ES, #[])) ?? "app"
    and abs sigma env () =
      (new_variable << spaces << symbol "." << spaces >>= (fn (n,v) =>
        let
          val sigma' = SymbolTable.bind sigma (n,v)
        in
          force (abt sigma' env) wth (fn E => v \\ E)
        end)) ?? "abs"
    and args sigma env () = separate (force (abt sigma env)) (symbol ";") wth Vector.fromList ?? "args"

  in
    fun parse_abt fvs env =
      force (abt (SymbolTable.empty fvs) env)

  end
end
