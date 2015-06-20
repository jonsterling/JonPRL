(* DEVELOPMENT models the aspect of Brouwer's Creating Subject which realizes
 * constructions over time. A value of type DEVELOPMENT.t is a stage in time at
 * which the knowledge of the creating subject may be queried, or to which new
 * knowledge may be added, resulting in another stage in time. In this sense,
 * the possible values of type DEVELOPMENT.t form a spread, whose law is
 * governed by the admissibility of new knowledge. *)

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
