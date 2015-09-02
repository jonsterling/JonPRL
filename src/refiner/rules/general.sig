signature GENERAL_RULES =
sig
  type tactic
  type term
  type hyp
  type name
  type conv
  type operator
  type world

  (* Pretend you have got a proof. *)
  val Fiat : tactic
  val Thin : hyp -> tactic
  val Lemma : world * operator -> tactic
  val Unfolds : world * (operator * Level.t option) list -> tactic
  val RewriteGoal : conv -> tactic
  val Witness : term -> tactic
  val Assumption : tactic
  val Assert : term * name option -> tactic
  val Hypothesis : hyp -> tactic
  val HypEq : tactic
  val Unhide : hyp -> tactic

  (* Match a single branch of a [match goal]. This needs to
   * be primitive because it needs access to the structure of
   * the sequent. It doesn't construct it's own validations
   * though. Perhaps we should move this out to REFINER_UTIL.
   *)
  val MatchSingle : (name * term) list * term * ((name * term) list -> tactic)
                    -> tactic
end
