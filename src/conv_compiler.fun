(* The idea is that whenever we find something that is a subst, then we will
 * compile it out in the conversion. *)
signature SO_TERM =
sig
  structure Operator : OPERATOR

  (* instantiate : (0;0) *)
  val asInstantiate : Operator.t -> unit option
end

functor ConvCompiler
  (structure Conv : CONV_TYPES
   structure SoTerm : SO_TERM
   structure Label : LABEL
   structure PatternSyntax : ABT_UTIL
     where type Operator.t = Label.t PatternOperatorType.operator
   val customOperator : Label.t * Arity.t -> Conv.Syntax.Operator.t
   sharing Conv.Syntax.Operator = SoTerm.Operator
   sharing Conv.Syntax.Variable = PatternSyntax.Variable) : CONV_COMPILER =
struct
  open Conv

  structure PatternSyntax = PatternSyntax
  structure Label = Label

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
  in
    fun compile {definiendum, definiens} = fn (M : Syntax.t) =>
      let
        val P.$ (PatternOperatorType.APP (lbl, arity), inargs) = P.out definiendum handle _ => raise Conv
        val S.$ (outop, outargs) = S.out definiens handle _ => raise Conv
        val S.$ (Mop, Margs) = S.out M handle _ => raise Conv

        val _ = if S.Operator.eq (customOperator (lbl, arity), Mop) then () else raise Conv
        val chart = computeChart (definiendum, M)

        open S
        infix $ $$ \ \\ //

        fun rewriteInstantiations M =
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
                             | _ => rewriteInstantiations E // M
                        end)
             | _ => raise Conv

        fun go H (p $ es) = p $$ Vector.map (go' H) es
          | go H (x \ E) = x \\ go' (Set.insert H x) E
          | go H (` x) =
              if Set.member H x then
                `` x
              else
                Dict.lookup chart x handle _ => `` x
        and go' H E = go H (out (CTRY rewriteInstantiations E))

        val res = go Set.empty (out definiens)
      in
        CDEEP rewriteInstantiations (go Set.empty (out definiens))
      end
  end

end

structure SoTerm : SO_TERM =
struct
  structure Operator = Syntax.Operator

  fun asInstantiate OperatorType.INSTANTIATE = SOME ()
    | asInstantiate _ = NONE
end

structure ConvCompiler = ConvCompiler
  (structure Conv = ConvTypes
   structure Label = StringVariable
   structure PatternSyntax = PatternSyntax
   structure SoTerm = SoTerm
   fun customOperator (lbl, arity) =
     OperatorType.CUSTOM {label = lbl, arity = arity})
