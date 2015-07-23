signature SO_TERM =
sig
  include ABT

  val asInstantiate : t -> (t * t) option
end

functor PatternCompiler
  (structure Conv : CONV
   structure SoTerm : SO_TERM

   type label
   sharing type Conv.term = SoTerm.t) : PATTERN_COMPILER =
struct
  structure S = AbtUtil(SoTerm)
  type term = S.t
  type pattern = S.t
  type rule = {definiendum : pattern, definiens : term}
  type conv = Conv.conv
  type label = label

  structure Set = SplaySet(structure Elem = S.Variable)
  structure Conversionals = Conversionals
    (structure Syntax = S
     structure Conv = Conv)

  exception InvalidTemplate

  datatype 'a point = GLOBAL of 'a | LOCAL of 'a -> 'a

  structure Chart =
  struct
    structure Dict = SplayDict(structure Key = S.Variable)
    open Dict

    type chart = S.t point dict
    fun lookupGlobal c x =
      case lookup c x of
           GLOBAL p => p
         | _ => raise Subscript

    fun lookupLocal c x =
      case lookup c x of
           LOCAL p => p
         | _ => raise Subscript
  end

  open S
  infix $ $$ \ \\

  fun computeChart (pat, N) : Chart.chart =
    case (out pat, out N) of
         (pato $ es, oper $ es') =>
           let
             val _ =
               if Operator.eq (pato, oper) then
                 ()
               else
                 raise InvalidTemplate

             open Vector
             val zipped = tabulate (length es, fn n => (sub (es, n), sub (es', n)))
             fun go (`x) E R = Chart.insert R x (GLOBAL (into E))
               | go (x \ M) (y \ N) R =
                 (case SoTerm.asInstantiate M of
                       SOME (F,X) =>
                         (case out F of
                               `f =>
                               if eq (``x,X) then
                                 Chart.insert R f (LOCAL (fn Z => subst Z y N))
                               else
                                 raise InvalidTemplate
                             | _ => raise InvalidTemplate)
                     | NONE => raise InvalidTemplate)
               | go _ _ _ = raise InvalidTemplate
           in
             foldl (fn ((e,e'), R') => go (out e) (out e') R') Chart.empty zipped
           end
       | _ => raise InvalidTemplate

  local
    open Conv Conversionals
  in
    fun compile ({definiendum, definiens} : rule) = fn (M : S.t) =>
      let
        val Pop $ _ = out definiendum
        val Mop $ _ = out M
        val chart = computeChart (definiendum, M)
      in
        case out definiens of
             ` x => (Chart.lookupGlobal chart x handle _ => ``x)
           | outop $ outargs =>
               let
                 val _ = if Operator.eq (Pop, Mop) then () else raise Conv
                 fun go H M =
                   case SoTerm.asInstantiate M of
                        NONE =>
                          (case out M of
                               p $ es => p $$ Vector.map (go H) es
                             | x \ E => x \\ go (Set.insert H x) E
                             | `x =>
                                 if Set.member H x then
                                   ``x
                                 else
                                   Chart.lookupGlobal chart x handle _ => ``x)
                      | SOME (F,X) =>
                          let
                            val `f = out F
                          in
                            Chart.lookupLocal chart f X
                          end
               in
                 go Set.empty definiens
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
   structure PatternSyntax = SoTerm
   structure SoTerm = SoTerm
   type label = string)
