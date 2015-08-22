structure Resource :> RESOURCE =
struct
  datatype t = AUTO | ELIM | EQ_CD | INTRO | WF

  fun toString AUTO = "auto"
    | toString ELIM = "elim"
    | toString EQ_CD = "eq-cd"
    | toString INTRO = "intro"
    | toString WF = "wf"

  open ParserCombinators CharParser JonprlTokenParser
  infix 2 return
  infixr 1 ||

  fun choices xs =
    foldl (fn (p, p') => p || try p') (fail "unknown operator") xs

  val parse =
    choices
      [string "auto" return AUTO,
       string "elim" return ELIM,
       string "eq-cd" return EQ_CD,
       string "intro" return INTRO,
       string "wf" return WF]
end
