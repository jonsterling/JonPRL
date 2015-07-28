functor PatternCompiler
  (structure Conv : CONV
   structure PatternTerm : PATTERN_TERM
   sharing type Conv.term = PatternTerm.t) : PATTERN_COMPILER =
struct
  structure PatternTerm = PatternTerm
  open PatternTerm

  type term = PatternTerm.t
  type pattern = PatternTerm.t
  type rule = {definiendum : pattern, definiens : term}
  type conv = Conv.conv

  structure Set = SplaySet(structure Elem = Variable)
  structure Conversionals = Conversionals
    (structure Syntax = PatternTerm
     structure Conv = Conv)

  exception InvalidTemplate

  structure Chart =
  struct
    structure Dict = SplayDict(structure Key = Variable)
    open Dict

    datatype 'a point =
        GLOBAL of 'a
        (* A "global" point is the definition of a first-order variable *)
      | LOCAL of 'a -> 'a
        (* A "local" point is the definition of a second-order variable *)

    type 'a chart = 'a point dict

    fun lookupGlobal c x =
      case lookup c x of
           GLOBAL p => p
         | _ => raise Subscript

    fun lookupLocal c x =
      case lookup c x of
           LOCAL p => p
         | _ => raise Subscript
  end

  structure AbtUtil = AbtUtil(PatternTerm)
  open AbtUtil
  infix $ $$ \ \\

  fun computeChart (pat, N) : term Chart.chart =
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

             (* If we are at a first-order variable, then insert its
              * substitution into the chart *)
             fun go (`x) E R = Chart.insert R x (Chart.GLOBAL (into E))
                 (* At an abstraction, the definiens shall be `x.F[x]`; the
                  * right hand side shall be y.E. So we insert its second order
                  * substitution into the chart, i.e. Z !-> [y/x]F. *)
               | go (x \ M) (y \ N) R =
                 (case PatternTerm.asInstantiate M of
                       SOME (F,X) =>
                         (case out F of
                               `f =>
                               if eq (``x,X) then
                                 Chart.insert R f (Chart.LOCAL (fn Z => subst Z y N))
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
    fun compile ({definiendum, definiens} : rule) = fn (M : term) =>
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
                   case PatternTerm.asInstantiate M of
                        NONE =>
                          (* If we have not reached a second-order application,
                           * then proceed structurally *)
                          (case out M of
                               p $ es => p $$ Vector.map (go H) es
                             | x \ E => x \\ go (Set.insert H x) E
                             | `x =>
                                 (* If we have a variable, see if it is from the
                                  * definiens and insert its substitution,
                                  * unless it is bound *)
                                 if Set.member H x then
                                   ``x
                                 else
                                   Chart.lookupGlobal chart x handle _ => ``x)
                      | SOME (F,X) =>
                           (* If we have got a second-order application, then
                            * apply its substitution *)
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

structure PatternTerm : PATTERN_TERM =
struct
  open CttCalculus CttCalculusInj Syntax
  structure CttView = RestrictAbtView (structure Abt = Syntax and Injection = CttCalculusInj)

  infix $ $$
  infixr \ \\

  local
    open CttView
  in
    fun asInstantiate M =
      case project M of
           SO_APPLY $ #[E, M] => SOME (E, M)
         | _ => NONE
  end

  fun patternForOperator theta =
    let
      val arity = Operator.arity theta
      val newVariable =
        let
          val store = ref (Variable.named "P")
        in
          fn () => let val name = ! store in store := Variable.prime name; `` name end
        end

      fun makeBoundVariables i =
        let
          fun go i xs =
            if i = 0 then
              xs
            else
              case xs of
                   [] => go (i - 1) [Variable.named "x"]
                 | y::ys => go (i - 1) (xs @ [Variable.prime y])
        in
          go i []
        end

      fun patternForValence i =
        let
          val xs = makeBoundVariables i
          val inner = foldl (fn (x,P) => `> SO_APPLY $$ #[P, ``x]) (newVariable ()) xs
        in
          foldr (fn (x, P) => x \\ P) inner xs
        end
    in
      theta $$ Vector.map patternForValence arity
    end
end

structure PatternCompiler = PatternCompiler
  (structure Conv = Conv
   structure PatternTerm = PatternTerm)
