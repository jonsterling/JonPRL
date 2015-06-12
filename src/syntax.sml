structure Syntax : PARSE_ABT =
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
      val parse_label : Label.t CharParser.charParser = identifier
    end

  end

  structure Operator = Operator (V)
  structure Abt = Abt
    (structure Operator = Operator
     structure Variable = Variable ())

  structure MyOp = Operator
  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = Operator)
  open ParseAbt OperatorType

  local
    infix $ \
    infix 8 $$ // \\
    open MyOp
  in
    val to_string =
    let
      fun enclose E =
        case out E of
             ` x => display E
           | O $ #[] => display E
           | _ => "(" ^ display E ^ ")"

      and display E =
        case out E of
             ISECT $ #[A,xB] =>
               let
                 val (x, B) = unbind xB
               in
                 "⋂" ^ Variable.to_string x ^ " ∈ " ^ display A ^ ". " ^ display B
               end

           | FUN $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "Π" ^ Variable.to_string x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " => " ^ display B
               end

           | PROD $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "Σ" ^ Variable.to_string x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " × " ^ display B
               end

           | SUBSET $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if has_free (B, x) then
                   "{" ^ Variable.to_string x ^ " ∈ " ^ display A ^ " | " ^ display B ^ "}"
                 else
                   "{" ^ display A ^ " | " ^ display B ^ "}"
               end


           | LAM $ #[xE] =>
               let
                 val (x, E) = unbind xE
               in
                 "λ" ^ dvar (x, E) ^ ". " ^ display E
               end

           | AP $ #[M, N] =>
               enclose M ^ "[" ^ display N ^ "]"

           | PAIR $ #[M, N] =>
               "⟨" ^ display M ^ ", " ^ display N ^ "⟩"

           | MEM $ #[M, A] =>
               display M ^ " ∈ " ^ display A

           | EQ $ #[M, N, A] =>
               display M ^ " = " ^ display N ^ " ∈ " ^ display A

           | UNIV i $ #[] =>
               "U" ^ subscript i

           | SPREAD $ #[M, xyN] =>
               let
                 val (x, yN) = unbind xyN
                 val (y, N) = unbind yN
               in
                 "let " ^ dvar (x, yN) ^ "," ^ dvar (y, N) ^ " = " ^ display M ^ " in " ^ display N
               end

           | _ => to_string_open display E

      and dvar (x, E) =
        if has_free (E, x) then Variable.to_string x else "_"

      and subscript i =
        case i of
             0 => "₀"
           | 1 => "₁"
           | 2 => "₂"
           | 3 => "₃"
           | 4 => "₄"
           | 5 => "₅"
           | 6 => "₆"
           | 7 => "₇"
           | 8 => "₈"
           | 9 => "₉"
           | _ => let val m = i mod 10 in subscript ((i - m) div 10) ^ subscript m end
    in
      display
    end
  end
end
