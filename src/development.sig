signature DEVELOPMENT =
sig
  type term
  type pattern
  type judgement
  type evidence

  type conv = term -> term
  type tactic

  structure Telescope : TELESCOPE
  type label = Telescope.label

  structure Object :
  sig
    type t
    val toString : label * t -> string
  end

  type t
  type object = Object.t

  val out : t -> object Telescope.telescope

  (* the empty development *)
  val empty : t

  (* extend a development with a theorem *)
  val prove : t -> label * judgement * tactic -> t
  exception RemainingSubgoals of judgement list

  (* extend a development with a custom tactic *)
  val defineTactic : t -> label * tactic -> t

  (* extend a development with a new operator *)
  val declareOperator : t -> label * Arity.t -> t
  val defineOperator : t -> {definiendum : pattern, definiens : term} -> t

  (* lookup the definiens *)
  val lookupDefinition : t -> label -> conv

  (* lookup the statement & evidence of a theorem *)
  val lookupTheorem : t -> label -> {statement : judgement, evidence : evidence Susp.susp}

  (* lookup a custom tactic *)
  val lookupTactic : t -> label -> tactic

  (* lookup a custom operator *)
  val lookupOperator : t -> label -> Arity.t
end
