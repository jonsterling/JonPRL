signature GENERAL_RULES =
sig
  type tactic
  type term
  type hyp
  type name
  type conv
  type operator
  type world

  val Witness : term -> tactic
  val Assumption : tactic
  val Assert : term * name option -> tactic
  val Hypothesis : hyp -> tactic
  val HypEq : tactic
  val MatchSingle : (name * term) list * term * ((name * term) list -> tactic)
                    -> tactic

  val Thin : hyp -> tactic
  val Fiat : tactic
  val RewriteGoal : conv -> tactic
  val Lemma : world * operator -> tactic
  val Unfolds : world * (operator * Level.t option) list -> tactic
end
