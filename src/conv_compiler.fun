signature SO_TERM =
sig
  structure Operator : OPERATOR

  (* instantiate : (0;0) *)
  val asInstantiate : Operator.t -> unit option
end

functor ConvCompiler
  (structure Conv : CONV_TYPES
   structure SoTerm : SO_TERM

   type label
   structure PatternSyntax : ABT_UTIL
     where type Operator.t = label PatternOperatorType.operator

   val customOperator : label * Arity.t -> Conv.Syntax.Operator.t

   sharing Conv.Syntax.Operator = SoTerm.Operator
   sharing Conv.Syntax.Variable = PatternSyntax.Variable) : CONV_COMPILER =
struct
  open Conv

  structure PatternSyntax = PatternSyntax
  type label = label

  structure S = Conv.Syntax and P = PatternSyntax
  type rule = {definiendum : PatternSyntax.t, definiens : Syntax.t }

  structure Set = SplaySet(structure Elem = S.Variable)
  structure Dict = SplayDict(structure Key = S.Variable)
  structure Conversionals = Conversionals
    (structure Syntax = Conv.Syntax
     structure ConvTypes = Conv)

  exception InvalidTemplate

  type chart = S.t Dict.dict

  fun computeChart (pat, N) : chart =
    case (P.out pat, S.out N) of
         (P.$ (PatternOperatorType.APP (lbl,arity), es), S.$ (oper, es')) =>
           let
             val _ =
               if S.Operator.eq (customOperator (lbl, arity), oper) then
                 ()
               else
                 raise InvalidTemplate

             open Vector
             val zipped = tabulate (length es, fn n => (sub (es, n), sub (es', n)))
             fun go (P.`x) E R = Dict.insert R x (S.into E)
               | go _ _ _ = raise InvalidTemplate
           in
             foldl (fn ((e,e'), R') => go (P.out e) (S.out e') R') Dict.empty zipped
           end

       | _ => raise InvalidTemplate

  local
    open Conversionals
    fun rewriteInstantiations chart M =
      let
        open S
        infix $ $$ \ \\ //
      in
        case out M of
             p $ es =>
               (case SoTerm.asInstantiate p of
                    NONE => raise Conv
                  | SOME () =>
                      let
                        val #[E, M] = es
                      in
                        case out E of
                             `sovar => Dict.lookup chart sovar // M
                           | _ => raise Conv
                      end)
           | _ => raise Conv
      end
  in
    fun compile {definiendum, definiens} = fn (M : Syntax.t) =>
      let
        val P.$ (PatternOperatorType.APP (lbl, arity), inargs) = P.out definiendum
        val S.$ (Mop, Margs) = S.out M
        val chart = computeChart (definiendum, M)
      in
        case S.out definiens of
             S.` x => (Dict.lookup chart x handle _ => S.``x)
           | S.$ (outop, outargs) =>
               let
                 val _ = if S.Operator.eq (customOperator (lbl, arity), Mop) then () else raise Conv
                 open S
                 infix $ $$ \ \\ //
                 fun go H (p $ es) = p $$ Vector.map (go' H) es
                   | go H (x \ E) = x \\ go' (Set.insert H x) E
                   | go H (` x) =
                       if Set.member H x then
                         `` x
                       else
                         Dict.lookup chart x handle _ => `` x
                 and go' H E = go H (out (CTRY (rewriteInstantiations chart) E))
                 val res = go Set.empty (out definiens)
               in
                 CDEEP (rewriteInstantiations chart) (go Set.empty (out definiens))
                 handle e => (print (exnMessage e); raise e)
               end
           | _ => raise Conv
      end
  end

end

structure SoTerm : SO_TERM =
struct
  structure Operator = Syntax.Operator

  fun asInstantiate OperatorType.SO_APPLY = SOME ()
    | asInstantiate _ = NONE
end

structure ConvCompiler = ConvCompiler
  (structure Conv = ConvTypes
   structure PatternSyntax = PatternSyntax
   structure SoTerm = SoTerm
   type label = string
   fun customOperator (lbl, arity) =
     OperatorType.CUSTOM {label = lbl, arity = arity})
