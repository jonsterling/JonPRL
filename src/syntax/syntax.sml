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
    open JonprlTokenParser
    open ParserCombinators CharParser ParserKit
    infix 2 wth suchthat return guard when
    infixr 1 ||
    infixr 4 << >>
    infix 2 -- ##
    infixr 3 &&
    infix $$ \\
  in
    val indFunOpr =
      (spaces >> symbol "->" >> spaces) return Infix (Right, 9, fn (A,B) => FUN $$ #[A, Variable.named "_" \\ B])
    val indIsectOpr =
      (spaces >> symbol "=>" >> spaces) return Infix (Right, 9, fn (A,B) => ISECT $$ #[A, Variable.named "_" \\ B])
    val indProdOpr =
      (spaces >> symbol "*" >> spaces) return Infix (Right, 10, fn (A,B) => PROD $$ #[A, Variable.named "_" \\ B])

    fun parseRaw w st () =
      fancySubset w st
      || fancyProd w st
      || fancyFun w st
      || fancyIsect w st
      || ParseAbt.extensibleParseAbt w (parseAbt w) st
    and fancyQuantifier w st (wrap, sep, oper) =
      wrap (parseBoundVariable st && colon >> parseAbt w st) << sep -- (fn ((x, st'), A) =>
        parseAbt w st' wth (fn B =>
          oper $$ #[A, x \\ B]))
    and fancyFun w st = fancyQuantifier w st (parens, opt (symbol "->") return (), FUN)
    and fancyIsect w st = fancyQuantifier w st (braces, opt (symbol "->") return (), ISECT)
    and fancyProd w st = fancyQuantifier w st (parens, symbol "*" return (), PROD)
    and fancySubset w st = braces (fancyQuantifier w st (fn x => x, symbol "|" return (), SUBSET))
    and parenthetical w st () = parens (parseAbt w st)
    and fixityItem w st =
      alt [indFunOpr, indIsectOpr, indProdOpr] wth Opr
      || alt [$ (parseRaw w st), $ (parenthetical w st)] wth Atm
    and parseAbt w st = spaces >> parsefixityadj (fixityItem w st) Left (fn (M,N) => AP $$ #[M,N]) << spaces
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
                 if hasFree (B, x) then
                   "{" ^ Variable.toString x ^ " : " ^ display A ^ "} " ^ display B
                 else
                   enclose A ^ " => " ^ display B
               end

           | FUN $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 if hasFree (B, x) then
                   "(" ^ Variable.toString x ^ " : " ^ display A ^ ") " ^ display B
                 else
                   enclose A ^ " -> " ^ display B
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
