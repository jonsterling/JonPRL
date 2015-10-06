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

  (* H, [z : A], J >> a = b in T
   *   H, z : A, J >> a = b inT *)
  val Unhide : hyp -> tactic

  (* H, z : A, J >> P
   *   H, a : Base, c : a ∈ A >> P[z\a]
   *   H, a : Base, b : Base, c : a = b ∈ A >> P[z\a] = P[z\b] ∈ U{k} *)
  val PointwiseFunctionality : (hyp * (name * name * name) option * Level.t option) -> tactic

  (* Match a single branch of a [match goal]. This needs to
   * be primitive because it needs access to the structure of
   * the sequent. It doesn't construct it's own validations
   * though. Perhaps we should move this out to REFINER_UTIL.
   *)
  val MatchSingle : (name * term) list * term * ((name * term) list -> tactic)
                    -> tactic
end
