(* DEVELOPMENT models the aspect of Brouwer's Creating Subject which realizes
 * constructions over time. A value of type DEVELOPMENT.world is a stage in time at
 * which the knowledge of the creating subject may be queried, or to which new
 * knowledge may be added, which are accessible at a new stage. In this sense,
 * the possible values of type DEVELOPMENT.world form a spread, whose law is
 * governed by the admissibility of new knowledge. *)

signature DEVELOPMENT =
sig
  type world
  type judgement
  type evidence
  type tactic

  type term
  type pattern

  type conv = term -> term

  structure Telescope : TELESCOPE
  type label = Telescope.label

  (* TODO: don't include this in this signature *)
  structure Object :
  sig
    type t
    val toString : label * t -> string
  end

  type object = Object.t

  (* enumerate the objects and knowledge available at a world *)
  val enumerate : world -> object Telescope.telescope

  (* the empty world *)
  val empty : world

  (* extend a development with a theorem *)
  val prove : world -> label * judgement * tactic -> world
  exception RemainingSubgoals of judgement list

  (* extend a development with a custom tactic *)
  val defineTactic : world -> label * tactic -> world

  (* extend a development with a new operator *)
  val declareOperator : world -> label * Arity.t -> world
  val defineOperator : world -> {definiendum : pattern, definiens : term} -> world

  (* lookup the definiens *)
  val lookupDefinition : world -> label -> conv

  (* lookup the statement & evidence of a theorem *)
  val lookupTheorem : world -> label -> {statement : judgement, evidence : evidence Susp.susp}

  (* lookup a custom tactic *)
  val lookupTactic : world -> label -> tactic

  (* lookup a custom operator *)
  val lookupOperator : world -> label -> Arity.t
end
