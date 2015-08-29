structure Syntax : PARSE_ABT =
struct
  structure V = StringVariable

  structure Abt = Abt
    (structure Operator = UniversalOperator
     structure Variable = Variable ())

  structure ParseAbt = ParseAbt
    (structure Syntax = AbtUtil(Abt)
     structure Operator = ParseOperator)
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

    fun forceBinding M =
      case out M of
           Abt.\ _ => M
         | _ => Abt.Variable.named "_" \\ M

    val extendOpr =
      (spaces >> (symbol "⌢" || symbol "^") >> spaces) return Infix (Left, 10, fn (A,B) => `> EXTEND $$ #[A, forceBinding B])

    fun customOperator w =
      (spaces >> identifier << spaces) -- (fn sym =>
        (let
          open Notation ParserContext
          val label = lookupNotation w sym
          val (theta, SOME notation) = ParserContext.lookupOperator w label
        in
          case notation of
               INFIX (_, assoc, i) =>
                 succeed (Infix (assoc, i, fn (M,N) => theta $$ #[M,N]))
             | PREFIX (_, i) =>
                 succeed (Prefix (i, fn M => theta $$ #[M]))
             | POSTFIX (_, i) =>
                 succeed (Postfix (i, fn M => theta $$ #[M]))
        end) handle _ => fail "not a custom notation")

    val pipe = symbol "|"
    fun pipes p = middle pipe p pipe

    fun parseRaw w st () =
      fancySubset w st
      || fancyProd w st
      || fancyFun w st
      || fancyIsect w st
      || fancyPair w st
      || fancyDom w st
      || fancyMakeContainer w st
      || matchToken w st
      || matchTokenBinding w st
      || ParseAbt.extensibleParseAbt w (parseAbt w) st
    and fancyQuantifier w st (wrap, sep, theta) =
      wrap (parseBoundVariable st && colon >> parseAbt w st) << sep -- (fn ((x, st'), A) =>
        parseAbt w st' wth (fn B =>
          `> theta $$ #[A, x \\ B]))
    and fancyFun w st = fancyQuantifier w st (parens, opt (symbol "->") return (), FUN)
    and fancyIsect w st = fancyQuantifier w st (braces, opt (symbol "->") return (), ISECT)
    and fancyProd w st = fancyQuantifier w st (parens, symbol "*" return (), PROD)
    and fancySubset w st = braces (fancyQuantifier w st (fn x => x, symbol "|" return (), SUBSET))
    and fancyMakeContainer w st = fancyQuantifier w st (fn x => x, (symbol "◃" || symbol "<:") return (), MAKE_CONTAINER)
    and fancyPair w st =
      brackets (commaSep (parseAbt w st)) wth rev --
        (fn [] => fail "Not enough components to product"
          | [x] => fail "Not enough components to product"
          | x::xs => succeed (foldl (fn (a,P) => `> PAIR $$ #[a,P]) x xs))
    and fancyDom w st =
      pipes (parseAbt w st) wth (fn M => `> DOM $$ #[M])
    and soAppOpr w st () =
      squares (parseAbt w st) wth (fn N => Postfix (12, fn M => `> SO_APPLY $$ #[M,N]))
    and parenthetical w st () = parens (parseAbt w st)
    and fixityItem w st =
      alt [customOperator w, plusOpr, extendOpr, indFunOpr, indIsectOpr, indProdOpr, $ (soAppOpr w st)] wth Opr
      || alt [$ (parseRaw w st), $ (parenthetical w st)] wth Atm
    and matchToken w st =
      symbol "match"
        >> parseAbt w st
        && braces (((sepEnd1 (matchTokenBranch w st) pipe) || succeed []) && matchTokenCatchAll w st)
        wth (fn (z, (branches, catchAll)) =>
          `> (MATCH_TOKEN (Vector.fromList (List.map #1 branches)))
              $$ Vector.fromList (z :: List.map #2 branches @ [catchAll]))
    and matchTokenBinding w st =
      symbol "match"
        >> braces (((sepEnd1 (matchTokenBranch w st) pipe) || succeed []) && matchTokenCatchAll w st)
        wth (fn (branches, catchAll) =>
          let
            val z = Abt.Variable.named "z"
          in
            z \\ (`> (MATCH_TOKEN (Vector.fromList (List.map #1 branches)))
                  $$ Vector.fromList ((`` z) :: List.map #2 branches @ [catchAll]))
          end)
    and matchTokenBranch w st = stringLiteral << symbol "=>" && parseAbt w st
    and matchTokenCatchAll w st = symbol "_" >> symbol "=>" >> parseAbt w st
    and parseAbt w st = spaces >> parsefixityadj (fixityItem w st) Left (fn (M,N) => `> AP $$ #[M,N]) << spaces
  end

  structure UnparseAbt : UNPARSE_ABT =
  struct
    infix $ \
    infix 8 $$ // \\
    open UniversalOperator CttCalculusInj

    structure UnparseAbt = UnparseAbt (structure Abt = Abt and Unparse = Unparse)
    open UnparseAbt

    structure CttCalculusView = RestrictAbtView
      (structure Abt = Abt and Injection = CttCalculusInj)

    fun unparseCttTerm M =
      let
        open CttCalculusView
      in
        case project M of
             AP $ #[M, N] => Unparse.adj (unparseAbt M, unparseAbt N)
           | FUN $ #[A, xB] =>
               let
                 val (x,B) = unbind xB
               in
                 if hasFree (B, x) then
                   Unparse.atom
                     ("(" ^ Variable.toString x ^ ":" ^ toString A ^ ") " ^ toString B)
                 else
                   Unparse.infix' (Unparse.Right, 9, "->") (unparseAbt A, unparseAbt B)
               end
           | ISECT $ #[A, xB] =>
               let
                 val (x,B) = unbind xB
               in
                 if hasFree (B, x) then
                   Unparse.atom
                     ("{" ^ Variable.toString x ^ ":" ^ toString A ^ "} " ^ toString B)
                 else
                   Unparse.infix' (Unparse.Right, 9, "=>") (unparseAbt A, unparseAbt B)
               end
           | PROD $ #[A, xB] =>
               let
                 val (x,B) = unbind xB
               in
                 if hasFree (B, x) then
                   Unparse.atom
                     ("(" ^ Variable.toString x ^ ":" ^ toString A ^ ") * " ^ toString B)
                 else
                   Unparse.infix' (Unparse.Right, 10, "*") (unparseAbt A, unparseAbt B)
               end
           | SUBSET $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 Unparse.atom
                   ("{" ^ Variable.toString x ^ ":" ^ toString A ^ " | " ^ toString B ^ "}")
               end
           | MAKE_CONTAINER $ #[A, xB] =>
               let
                 val (x, B) = unbind xB
               in
                 Unparse.atom
                   (Variable.toString x ^ ":" ^ toString A ^ " <: " ^ toString B)
               end
           | DOM $ #[F] =>
               Unparse.atom ("|" ^ toString F ^ "|")
           | PLUS $ #[A,B] =>
               Unparse.infix' (Unparse.Right, 8, "+") (unparseAbt A, unparseAbt B)
           | EXTEND $ #[S, rR] =>
               let
                 val (r, R) = unbind rR
                 val R' = if hasFree (R, r) then rR else R
               in
                 Unparse.infix' (Unparse.Right, 10, "^") (unparseAbt S, unparseAbt R')
               end
           | PAIR $ #[M,N] =>
               Unparse.atom ("<" ^ toString M ^ ", " ^ toString N ^ ">")
           | MATCH_TOKEN toks $ es =>
               let
                 val target = Vector.sub (es, 0)
                 val branches =
                   Vector.tabulate
                    (Vector.length es - 2,
                     fn i => (Vector.sub (toks, i), Vector.sub (es, i + 1)))
                 val catchAll = Vector.sub (es, Vector.length es - 1)
                 val printedBranches =
                   Vector.foldr
                    (fn ((tok, E), str) => "\"" ^ tok ^ "\" => " ^ toString E ^ " | " ^  str)
                    ("_ => " ^ toString catchAll)
                    branches
               in
                 Unparse.atom ("match " ^ toString target ^ " {" ^ printedBranches ^ "}")
               end
           | SO_APPLY $ #[M,N] =>
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
