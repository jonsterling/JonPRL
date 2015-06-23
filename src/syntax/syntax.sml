structure Syntax : PARSE_ABT =
struct
  structure V = ParseLabel (StringVariable)

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
    val toString =
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
                 "⋂" ^ Variable.toString x ^ " ∈ " ^ display A ^ ". " ^ display B
               end

           | FUN $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if hasFree (B, x) then
                   "Π" ^ Variable.toString x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " => " ^ display B
               end

           | PROD $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if hasFree (B, x) then
                   "Σ" ^ Variable.toString x ^ " ∈ " ^ display A ^ ". " ^ display B
                 else
                   enclose A ^ " × " ^ display B
               end

           | SUBSET $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if hasFree (B, x) then
                   "{" ^ Variable.toString x ^ " ∈ " ^ display A ^ " | " ^ display B ^ "}"
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

           | _ => toStringOpen display E

      and dvar (x, E) =
        if hasFree (E, x) then Variable.toString x else "_"

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

structure Conv = Conv(Syntax)
