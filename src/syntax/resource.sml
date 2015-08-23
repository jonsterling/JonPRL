structure Resource :> RESOURCE =
struct
  structure Variable = Variable ()

  datatype t = AUTO | ELIM | EQ_CD | INTRO | CUSTOM of Variable.t

  fun toString AUTO = "auto"
    | toString ELIM = "elim"
    | toString EQ_CD = "eq-cd"
    | toString INTRO = "intro"
    | toString (CUSTOM v) = Variable.toString v

  open ParserCombinators CharParser JonprlTokenParser
  infix 2 return wth
  infixr 1 ||

  fun choices xs =
    foldl (fn (p, p') => p || try p') (fail "unknown operator") xs

  fun parse lookupCustom =
    choices
      [string "auto" return AUTO,
       string "elim" return ELIM,
       string "eq-cd" return EQ_CD,
       string "intro" return INTRO,
       identifier wth lookupCustom]
end
