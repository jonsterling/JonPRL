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
    open ParserCombinators CharParser ParserKit
    infix 2 wth suchthat return guard when
    infixr 1 ||
    infixr 4 << >>
    infix 2 -- ##
    infixr 3 &&
    infix $$ \\
  in
    fun parseRaw w st = ParseAbt.extensibleParseAbt w (parseAbt w) st
    and parenthetical w st () = string "(" >> parseAbt w st << string ")" << spaces
    and expItem w st = (parseRaw w st || $ (parenthetical w st)) wth Atm
    and parseAbt w st = parsefixityadj (expItem w st) Left (fn (M,N) => AP $$ #[M,N])
  end

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
               "U{" ^ Level.toString i ^ "}"

           | _ => toStringOpen display E

      and dvar (x, E) =
        if hasFree (E, x) then Variable.toString x else "_"
    in
      display
    end
  end
end

structure Conv = Conv(Syntax)
