functor UnifyLevel (Syntax : SYNTAX_WITH_UNIVERSES) :>
  UNIFY_LEVEL
    where type term = Syntax.Abt.t
    where Level = Syntax.Level =
struct
  structure Syntax = Syntax
  open Syntax Syntax.Abt

  infix $ \

  type term = Syntax.Abt.t
  exception UnifyLevel

  local
    structure Dict = SplayDict(structure Key = Variable)
    open Dict

    fun go H (` x, ` y) R =
          let
            open Variable
          in
            if eq (x, y) orelse eq (lookup H x, y) orelse eq (lookup H y, x) then
              R
            else
              raise UnifyLevel
          end
      | go H (x \ E, y \ F) R = go (insert H x y) (out E, out F) R
      | go H (O1 $ ES1, O2 $ ES2) R =
          (case (View.out O1, View.out O2) of
                (View.UNIV k, View.UNIV l) => goes H (ES1, ES2) (Level.unify (k,l) :: R)
              | (View.OTHER O1', View.OTHER O2') =>
                  if Operator.eq (O1', O2') then
                    goes H (ES1, ES2) R
                  else
                    raise UnifyLevel
              | _ => raise UnifyLevel)
      | go _ _ _ = raise UnifyLevel
    and goes H (xs, ys) R =
          let
            val length = Vector.length xs
            val _ = if Vector.length ys <> length then raise UnifyLevel else ()
            val xsys = Vector.tabulate (length, fn n => (Vector.sub (xs, n), Vector.sub (ys, n)))
          in
            Vector.foldl (fn ((M,N), R') => go H (out M, out N) R') R xsys
          end
  in
    fun unify_level (M, N) = go empty (out M, out N) []
  end

  fun subst f M =
    case out M of
         ` x => into (` x)
       | O $ ES => into (map_level f O $ Vector.map (subst f) ES)
       | x \ E => into (x \ subst f E)
end

functor UnifyLevelSequent
  (structure Unify : UNIFY_LEVEL
   structure Abt : ABT
   structure Sequent : SEQUENT
   sharing type Abt.t = Unify.term
   sharing type Sequent.term = Unify.term) : UNIFY_LEVEL =
struct
  structure Level = Unify.Level
  structure Unify = Unify
  structure Sequent = Sequent

  open Sequent
  infix >>

  open Unify
  type term = Sequent.sequent

  local
    open Context.Telescope
    fun go (H, H') R =
      case ConsView.out H of
           ConsView.Empty => R
         | ConsView.Cons (lbl, (A, vis), tel) =>
             go (tel, H') (R @ Unify.unify_level (A, Context.lookup H lbl))
  in
    fun ctx_unify_level (H, H') = go (H, H') []
  end

  fun unify_level (H >> C, H' >> C') =
    Unify.unify_level (C, C')
      @ ctx_unify_level (H, H')

  fun subst f (H >> C) =
    Context.map (Unify.subst f) H >> Unify.subst f C
end

functor SyntaxWithUniverses
  (Syntax : ABT where Operator = Operator)
    :> SYNTAX_WITH_UNIVERSES where Level = Level and Abt = Syntax =
struct
  structure Level = Level
  structure Abt = Syntax

  fun map_level f O =
    case O of
         Operator.UNIV k => Operator.UNIV (Level.subst f k)
       | Operator.UNIV_EQ k => Operator.UNIV_EQ (Level.subst f k)
       | _ => O

  structure View =
  struct
    datatype 'a operator =
        UNIV of Level.t
      | OTHER of 'a

    fun out (Operator.UNIV k) = UNIV k
      | out (Operator.UNIV_EQ k) = UNIV k
      | out O = OTHER O
  end
end
