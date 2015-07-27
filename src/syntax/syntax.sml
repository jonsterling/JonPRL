structure Syntax : PARSE_ABT =
struct
  structure V = ParseLabel (StringVariable)

  structure Abt = Abt
    (structure Operator = UniversalOperator
     structure Variable = Variable ())

  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = UniversalOperator)
  open CttCalculus ParseAbt


  local
    open JonprlTokenParser
    open ParserCombinators CharParser ParserKit
    open CttCalculusInj
    infix 2 wth suchthat return guard when
    infixr 1 ||
    infixr 4 << >>
    infix 2 -- ##
    infixr 3 &&
    infix $$ \\
  in
    val indFunOpr =
      (spaces >> symbol "->" >> spaces) return Infix (Right, 9, fn (A,B) => `> FUN $$ #[A, Variable.named "x" \\ B])
    val indIsectOpr =
      (spaces >> symbol "=>" >> spaces) return Infix (Right, 9, fn (A,B) => `> ISECT $$ #[A, Variable.named "x" \\ B])
    val indProdOpr =
      (spaces >> symbol "*" >> spaces) return Infix (Right, 11, fn (A,B) => `> PROD $$ #[A, Variable.named "x" \\ B])
    val plusOpr =
      (spaces >> symbol "+" >> spaces) return Infix (Right, 10, fn (A,B) => `> PLUS $$ #[A,B])

    fun customOperator w =
      (spaces >> identifier << spaces) -- (fn sym =>
        (let
          open Notation ParserContext
          val label = lookupNotation w sym
          val (arity, SOME notation) = ParserContext.lookupOperator w label
          val theta = `> (CUSTOM {label = label, arity = arity})
        in
          case notation of
               INFIX (_, assoc, i) =>
                 succeed (Infix (assoc, i, fn (M,N) => theta $$ #[M,N]))
             | PREFIX (_, i) =>
                 succeed (Prefix (i, fn M => theta $$ #[M]))
             | POSTFIX (_, i) =>
                 succeed (Postfix (i, fn M => theta $$ #[M]))
        end) handle _ => fail "not a custom notation")

    fun parseRaw w st () =
      fancySubset w st
      || fancyProd w st
      || fancyFun w st
      || fancyIsect w st
      || fancyPair w st
      || ParseAbt.extensibleParseAbt w (parseAbt w) st
    and fancyQuantifier w st (wrap, sep, theta) =
      wrap (parseBoundVariable st && colon >> parseAbt w st) << sep -- (fn ((x, st'), A) =>
        parseAbt w st' wth (fn B =>
          `> theta $$ #[A, x \\ B]))
    and fancyFun w st = fancyQuantifier w st (parens, opt (symbol "->") return (), FUN)
    and fancyIsect w st = fancyQuantifier w st (braces, opt (symbol "->") return (), ISECT)
    and fancyProd w st = fancyQuantifier w st (parens, symbol "*" return (), PROD)
    and fancySubset w st = braces (fancyQuantifier w st (fn x => x, symbol "|" return (), SUBSET))
    and fancyPair w st =
      brackets (commaSep (parseAbt w st)) wth rev --
        (fn [] => fail "Not enough components to product"
          | [x] => fail "Not enough components to product"
          | x::xs => succeed (foldl (fn (a,P) => `> PAIR $$ #[a,P]) x xs))
    and soAppOpr w st () =
      squares (parseAbt w st) wth (fn N => Postfix (12, fn M => `> SO_APPLY $$ #[M,N]))
    and parenthetical w st () = parens (parseAbt w st)
    and fixityItem w st =
      alt [customOperator w, plusOpr, indFunOpr, indIsectOpr, indProdOpr, $ (soAppOpr w st)] wth Opr
      || alt [$ (parseRaw w st), $ (parenthetical w st)] wth Atm
    and parseAbt w st = spaces >> parsefixityadj (fixityItem w st) Left (fn (M,N) => `> AP $$ #[M,N]) << spaces
  end

  structure UnparseAbt : UNPARSE_ABT =
  struct
    infix $ \
    infix 8 $$ // \\
    open UniversalOperator CttCalculusInj

    structure UnparseAbt = UnparseAbt (structure Abt = Abt and Unparse = Unparse)
    open UnparseAbt

    fun unparseCttTerm M =
      let
        val theta $ subterms = out M
      in
        case (`< theta, subterms) of
             (AP, #[M, N]) => Unparse.adj (unparseAbt M, unparseAbt N)
           | (FUN, #[A, xB]) =>
               let
                 val (x,B) = unbind xB
               in
                 if hasFree (B, x) then
                   Unparse.atom
                     ("(" ^ Variable.toString x ^ ":" ^ toString A ^ ") " ^ toString B)
                 else
                   Unparse.infix' (Unparse.Right, 9, "->") (unparseAbt A, unparseAbt B)
               end
           | (ISECT, #[A, xB]) =>
               let
                 val (x,B) = unbind xB
               in
                 if hasFree (B, x) then
                   Unparse.atom
                     ("{" ^ Variable.toString x ^ ":" ^ toString A ^ "} " ^ toString B)
                 else
                   Unparse.infix' (Unparse.Right, 9, "=>") (unparseAbt A, unparseAbt B)
               end
           | (PROD, #[A, xB]) =>
               let
                 val (x,B) = unbind xB
               in
                 if hasFree (B, x) then
                   Unparse.atom
                     ("(" ^ Variable.toString x ^ ":" ^ toString A ^ ") * " ^ toString B)
                 else
                   Unparse.infix' (Unparse.Right, 10, "*") (unparseAbt A, unparseAbt B)
               end
           | (SUBSET, #[A, xB]) =>
               let
                 val (x, B) = unbind xB
               in
                 Unparse.atom
                   ("{" ^ Variable.toString x ^ ":" ^ toString A ^ " | " ^ toString B ^ "}")
               end
           | (PLUS, #[A,B]) =>
               Unparse.infix' (Unparse.Right, 8, "+") (unparseAbt A, unparseAbt B)
           | (PAIR, #[M,N]) =>
               Unparse.atom ("<" ^ toString M ^ ", " ^ toString N ^ ">")
           | (SO_APPLY, #[M,N]) =>
               Unparse.postfix (12, "[" ^ toString N ^ "]") (unparseAbt M)
           | _ => inner M
      end
    and unparseAbt M =
      unparseCttTerm M
        handle _ => inner M
    and inner t = UnparseAbt.extensibleUnparseAbt unparseAbt t
    and toString t = Unparse.parens (Unparse.done (unparseAbt t))
  end

  val toString = UnparseAbt.toString
end

structure Conv = Conv(Syntax)
