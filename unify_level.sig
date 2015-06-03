signature UNIFY_LEVEL =
sig
  structure Level : LEVEL
  type term

  type constraint
  type substitution

  val yank : Level.t -> substitution

  exception UnifyLevel

  val unify_level : term * term -> constraint list
  val resolve : constraint list -> substitution
  val subst : substitution -> term -> term
end

signature SYNTAX_WITH_UNIVERSES =
sig
  structure Level : LEVEL
  structure Abt : ABT

  val map_level : (Level.t -> Level.t) -> Abt.Operator.t -> Abt.Operator.t

  structure View :
  sig
    datatype 'a operator =
        UNIV of Level.t
      | OTHER of 'a

    val out : Abt.Operator.t -> Abt.Operator.t operator
  end
end

