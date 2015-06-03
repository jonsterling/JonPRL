signature UNIFY_LEVEL =
sig
  structure Level : LEVEL
  type term

  exception UnifyLevel

  val unify_level : term * term -> Level.constraint list
  val subst : Level.substitution -> term -> term
end

signature SYNTAX_WITH_UNIVERSES =
sig
  structure Level : LEVEL
  structure Abt : ABT

  val map_level : Level.substitution -> Abt.Operator.t -> Abt.Operator.t

  structure View :
  sig
    datatype 'a operator =
        UNIV of Level.t
      | OTHER of 'a

    val out : Abt.Operator.t -> Abt.Operator.t operator
  end
end

