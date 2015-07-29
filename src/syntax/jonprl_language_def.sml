structure JonprlLanguageDef :> LANGUAGE_DEF =
struct
  open ParserCombinators CharParser
  infixr 1 ||

  type scanner = char charParser
  val commentStart = SOME "(*"
  val commentEnd = SOME "*)"
  val commentLine = SOME "|||"
  val nestedComments = false

  val fancyChars =
      "-'_ΑαΒβΓγΔδΕεΖζΗηΘθΙιΚκΛλΜμΝνΞξΟοΠπΡρΣσΤτΥυΦφΧχΨψΩω¬⊗⊕∫+-!@#$%^&*⇓↓↼⇀↽⇁↿↾⇃⇂≼≅≡≈~⇔"

  val identLetter = letter || oneOf (String.explode fancyChars) || digit
  val identStart = identLetter
  val opStart = fail "Operators not supported" : scanner
  val opLetter = opStart
  val reservedNames = []
  val reservedOpNames = []
  val caseSensitive = true
end

structure JonprlTokenParser :> TOKEN_PARSER = TokenParser (JonprlLanguageDef)
