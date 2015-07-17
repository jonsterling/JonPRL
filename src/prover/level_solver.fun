functor LevelSolver (Syntax : SYNTAX_WITH_UNIVERSES) :>
  LEVEL_SOLVER
    where type term = Syntax.t
    where type Level.t = Syntax.Level.t =
struct
  open Syntax

  infix $ \
  type term = Syntax.t

  exception LevelSolver

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
              raise LevelSolver
          end
      | go H (x \ E, y \ F) R = go (insert H x y) (out E, out F) R
      | go H (O1 $ ES1, O2 $ ES2) R =
        if eqModLevel (O1, O2) then
            case (getLevelParameter O1, getLevelParameter O2) of
                (SOME k, SOME l) => goes H (ES1, ES2) (Level.unify (k,l) :: R)
              | (NONE, NONE) => goes H (ES1, ES2) R
              | _ => raise LevelSolver
        else
            raise LevelSolver
      | go _ _ _ = raise LevelSolver
    and goes H (xs, ys) R =
          let
            val length = Vector.length xs
            val _ = if Vector.length ys <> length then raise LevelSolver else ()
            val xsys = Vector.tabulate (length, fn n => (Vector.sub (xs, n), Vector.sub (ys, n)))
          in
            Vector.foldl (fn ((M,N), R') => go H (out M, out N) R') R xsys
          end
  in
    fun generateConstraints (M, N) = go empty (out M, out N) []
  end

  fun subst f M =
    case out M of
         ` x => into (` x)
       | O $ ES => into (mapLevel f O $ Vector.map (subst f) ES)
       | x \ E => into (x \ subst f E)
end

functor SyntaxWithUniverses
  (type label
   structure Syntax : ABT
     where type Operator.t = label OperatorType.operator
  ) : SYNTAX_WITH_UNIVERSES =
struct
  open Syntax
  structure Level = Level

  fun mapLevel f O =
    case O of
         OperatorType.UNIV k => OperatorType.UNIV (Level.subst f k)
       | OperatorType.UNIV_EQ k => OperatorType.UNIV_EQ (Level.subst f k)
       | _ => O

  fun getLevelParameter (OperatorType.UNIV k) = SOME k
    | getLevelParameter (OperatorType.UNIV_EQ k) = SOME k
    | getLevelParameter _ = NONE

  fun eqModLevel (OperatorType.UNIV _, OperatorType.UNIV _) = true
    | eqModLevel (OperatorType.UNIV_EQ _, OperatorType.UNIV_EQ _) = true
    | eqModLevel (o1, o2) = Operator.eq (o1, o2)
end

functor SequentLevelSolver
  (structure Solver : LEVEL_SOLVER
   structure Abt : ABT where type t = Solver.term
   structure Sequent : SEQUENT where type term = Solver.term) : LEVEL_SOLVER =
struct
  structure Level = Solver.Level
  structure Solver = Solver
  structure Sequent = Sequent

  open Sequent
  infix >>

  open Solver
  type term = Sequent.sequent

  local
    open Context.Telescope
    fun go (H, H') R =
      case ConsView.out H of
           ConsView.Empty => R
         | ConsView.Cons (lbl, (A, vis), tel) =>
             go (tel, H')
               (R @ Solver.generateConstraints (A, Context.lookup H lbl))
  in
    fun ctxGenerateConstraints (H, H') = go (H, H') []
  end

  fun generateConstraints (H >> C, H' >> C') =
    Solver.generateConstraints (C, C')
      @ ctxGenerateConstraints (H, H')

  fun subst f (H >> C) =
    Context.map (Solver.subst f) H >> Solver.subst f C
end
