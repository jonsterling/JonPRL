functor ConvTypes (Syn : ABT_UTIL) : CONV_TYPES =
struct
  structure Syntax = Syn
  type conv = Syn.t -> Syn.t
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  open Syntax

  fun reductionRule red M = red (map out (out M))
  exception Conv
end

functor ConvCompiler (Conv : CONV_TYPES) : CONV_COMPILER =
struct
  open Conv

  type rule = {definiendum : Syntax.t, definiens : Syntax.t}

  open Conv.Syntax
  infix $ \ $$ \\

  structure Set = SplaySet(structure Elem = Variable)
  structure Dict = SplayDict(structure Key = Variable)

  exception InvalidTemplate

  fun computeChart (M,N) =
    case (out M, out N) of
         (p $ es, p' $ es') =>
           let
             val _ = if Operator.eq (p, p') then () else raise InvalidTemplate
             open Vector
             val zipped = tabulate (length es, fn n => (sub (es, n), sub (es', n)))

             fun go H (x \ E) (y \ E') R =
                 go (Set.insert H x) (out E) (out (subst (``x) y E')) R
               | go H (`x) E R =
                 if Set.member H x then
                   R
                 else
                   Dict.insert R x (into E)
               | go _ _ _ _ = raise InvalidTemplate

           in
             foldl (fn ((e,e'), R') => go Set.empty (out e) (out e') R') Dict.empty zipped
           end
       | _ => raise InvalidTemplate

  fun compile {definiendum, definiens} = fn (M : Syntax.t) =>
    let
      val inop $ inargs = out definiendum handle _ => raise Conv
      val outop $ outargs = out definiens handle _ => raise Conv
      val Mop $ MArgs = out M handle _ => raise Conv
      val _ = if Operator.eq (Mop, inop) then () else raise Conv
      val chart = computeChart (definiendum, M)

      fun go H (p $ es) = p $$ Vector.map (go H o out) es
        | go H (x \ E) = x \\ go (Set.insert H x) (out E)
        | go H (` x) =
            if Set.member H x then
              `` x
            else
              Dict.lookup chart x handle _ => `` x
    in
      go Set.empty (out definiens)
    end
end

structure ConvTypes = ConvTypes (Syntax)
structure ConvCompiler = ConvCompiler (ConvTypes)
