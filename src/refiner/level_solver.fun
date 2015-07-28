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

    (* go is the main helper functin for [generateConstraints]. For the most
     * part it simply walks down the ABTs on the left and right and assert
     * that they are alpha equivalent. The dictionary H specifies pairs of bound
     * of variables (one from the left and one from the right) that where bound
     * at the same point.
     *
     * The only place where it differs from ABT_UTIL.eq is in the case of
     * operators
     *)
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
      (* Since operators may contain levels, we don't want to assert that
       * they're equal. Rather, we assert they're equal discounting any
       * embedded levels and then (if they contain levels) unify those levels
       * and add that to our list of constraints.
       *)
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

  (* [subst f M] walks M and add each operator [O $ ES] applies [mapLevel f] to
   * [O] before proceeding. In this way it applies the substitution to all
   * possible embedded levels.
   *)
  fun subst f M =
    case out M of
         ` x => into (` x)
       | O $ ES => into (mapLevel f O $ Vector.map (subst f) ES)
       | x \ E => into (x \ subst f E)
end

functor SyntaxWithUniverses (Syntax : ABT where type Operator.t = UniversalOperator.t) : SYNTAX_WITH_UNIVERSES =
struct
  open CttCalculus
  open Derivation

  open Syntax
  structure Level = Level

  structure C = CttCalculusInj
  structure D = DerivationInj

  fun mapLevel f theta =
    case C.`<? theta of
         SOME (UNIV k) => C.`> (UNIV (Level.subst f k))
       | _ =>
           (case D.`<? theta of
                 SOME (UNIV_EQ k) => D.`> (UNIV_EQ (Level.subst f k))
               | _ => theta)

  fun getLevelParameter theta =
    case C.`<? theta of
         SOME (UNIV k) => SOME k
       | _ =>
           (case D.`<? theta of
                 SOME (UNIV_EQ k) => SOME k
               | _ => NONE)

  fun eqModLevel (theta, theta') =
    case (C.`<? theta, C.`<? theta') of
         (SOME (UNIV _), SOME (UNIV _)) => true
       | _ =>
           (case (D.`<? theta, D.`<? theta') of
                 (SOME (UNIV_EQ _), SOME (UNIV_EQ _)) => true
               | _ => Operator.eq (theta, theta'))
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

  (* [ctxGenerateConstraints] generates level constraints for contexts by
   * by looking up every member of [H] in [H'] and constraining them using
   * the supplied [Solver]. Note that this means that we only need to know
   * that [H] is a subset of [H'], not that they're completely equal.
   *)
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

  (* subst uses [Solver.subst] to apply the substitution to everything
   * in the context as well as the goal.
   *)
  fun subst f (H >> C) =
    Context.map (Solver.subst f) H >> Solver.subst f C
end
