signature SO_TERM =
sig
  include ABT

  val asInstantiate : t -> (t * t) option
end

functor PatternCompiler
  (structure Conv : CONV
   structure SoTerm : SO_TERM

   type label
   structure PatternSyntax : ABT_UTIL
     where type Operator.t = SoTerm.Operator.t

   sharing type Conv.term = SoTerm.t
   sharing type SoTerm.Variable.t = PatternSyntax.Variable.t) : PATTERN_COMPILER =
struct
  structure PatternSyntax = PatternSyntax
  structure S = AbtUtil(SoTerm) and P = PatternSyntax
  type term = S.t
  type pattern = P.t
  type rule = {definiendum : pattern, definiens : term}
  type conv = Conv.conv
  type label = label

  structure Set = SplaySet(structure Elem = S.Variable)
  structure Dict = SplayDict(structure Key = S.Variable)
  structure Conversionals = Conversionals
    (structure Syntax = S
     structure Conv = Conv)

  exception InvalidTemplate

  type chart = S.t Dict.dict

  fun computeChart (pat, N) : chart =
    case (P.out pat, S.out N) of
         (P.$ (pato, es), S.$ (oper, es')) =>
           let
             val _ =
               if S.Operator.eq (pato, oper) then
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
    open Conv Conversionals
    fun rewriteInstantiations chart M =
      let
        open S
        infix $ $$ \ \\ //
      in
        case SoTerm.asInstantiate M of
             NONE => raise Conv
           | SOME (E, M) =>
               (case out E of
                     `sovar => Dict.lookup chart sovar // M
                   | _ => raise Conv)
      end
  in
    fun compile ({definiendum, definiens} : rule) = fn (M : S.t) =>
      let
        val P.$ (Pop, _) = P.out definiendum
        val S.$ (Mop, _) = S.out M
        val chart = computeChart (definiendum, M)
      in
        case S.out definiens of
             S.` x => (Dict.lookup chart x handle _ => S.``x)
           | S.$ (outop, outargs) =>
               let
                 val _ = if S.Operator.eq (Pop, Mop) then () else raise Conv
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
               end
           | _ => raise Conv
      end
  end

end

structure SoTerm : SO_TERM =
struct
  open Syntax
  infix $

  fun asInstantiate M =
    case out M of
         OperatorType.SO_APPLY $ #[E, M] => SOME (E, M)
       | _ => NONE
end

structure PatternCompiler = PatternCompiler
  (structure Conv = Conv
   structure PatternSyntax = PatternSyntax
   structure SoTerm = SoTerm
   type label = string)
