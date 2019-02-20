signature LEVEL_SOLVER =
sig
  structure Level : LEVEL
  type term

  exception LevelSolver

  (* Given two terms, generate a list of constraints if the two
   * terms are the same modulo the levels in each term. The constraints
   * in this list are generated by applying [Level.unify] to the pairs
   * of levels in the terms.
   *)
  val generateConstraints : term * term -> Level.constraint list

  (* Given a substitution, walk a term and apply it to the
   * the levels embedded in the terms.
   *)
  val subst : Level.substitution -> term -> term
end

(* This supplements normal ABTs to handle operators which
 * may have levels embedded inside them. For example, JonPRL's
 * term ABT has levels in the [UNIV] operator among others.
 *)
signature SYNTAX_WITH_UNIVERSES =
sig
  include ABT
  structure Level : LEVEL

  val mapLevel : Level.substitution -> Operator.t -> Operator.t
  val getLevelParameter : Operator.t -> Level.t option
  val eqModLevel : Operator.t * Operator.t -> bool
end