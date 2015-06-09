functor ConvTypes (Syn : ABT_UTIL) : CONV_TYPES =
struct
  structure Syntax = Syn
  type conv = Syn.t -> Syn.t
  type red = Syntax.t Syntax.view Syntax.view -> Syntax.t

  open Syntax

  fun reduction_rule red M = red (map out (out M))
  exception Conv
end

functor ConvCompiler (Conv : CONV_TYPES) : CONV_COMPILER =
struct
  open Conv

  type rule = {input : Syntax.t, output : Syntax.t}

  open Conv.Syntax
  infix $ \ $$ \\

  exception Hole

  structure Set = SplaySet(structure Elem = Variable)
  structure Dict = SplayDict(structure Key = Variable)

  exception InvalidTemplate
  fun compute_chart (template, term) =
    let
      fun go H (p $ es) (p' $ es') R =
          if Operator.eq (p, p') then
            let
              open Vector
              val zipped = tabulate (length es, fn n => (sub (es, n), sub (es', n)))
            in
              foldl (fn ((e,e'), R') => go H (out e) (out e') R') R zipped
            end
          else
            raise InvalidTemplate
        | go H (x \ E) (y \ E') R =
          go (Set.insert H x) (out E) (out (subst (``x) y E')) R
        | go H (`x) E R =
          if Set.member H x then
            R
          else
            Dict.insert R x (into E)
        | go _ _ _ _ = raise InvalidTemplate
    in
      go Set.empty (out template) (out term) Dict.empty
    end

  fun compile {input, output} = fn (M : Syntax.t) =>
    let
      val inop $ inargs = out input handle _ => raise Conv
      val outop $ outargs = out output handle _ => raise Conv
      val Mop $ M_args = out M handle _ => raise Conv
      val _ = if Operator.eq (Mop, inop) then () else raise Conv
      val chart = compute_chart (input, M)

      fun go H (p $ es) = p $$ Vector.map (go H o out) es
        | go H (x \ E) = x \\ go (Set.insert H x) (out E)
        | go H (` x) =
            if Set.member H x then
              go H (` x)
            else
              Dict.lookup chart x handle _ => `` x
    in
      go Set.empty (out output)
    end
end

structure ConvTypes = ConvTypes (Syntax)
structure ConvCompiler = ConvCompiler (ConvTypes)
