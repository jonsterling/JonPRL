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
  type resource

  type term
  type operator

  type conv = term -> term

  structure Telescope : TELESCOPE
    where type Label.t = Label.t
  type label = Telescope.label

  structure Object :
  sig
    type theorem
    type operator_decl

    datatype 'a t =
        THEOREM of theorem
      | TACTIC of 'a -> tactic
      | OPERATOR of operator_decl

    val toString : label * 'a t -> string
  end

  type object = world Object.t

  (* enumerate the objects and knowledge available at a world *)
  val enumerate : world -> object Telescope.telescope
  val enumerateOperators : world -> (label * operator * Notation.t option) list
  val enumerateTactics : world -> label list
  val enumerateResources : world -> Resource.t list

  (* the empty world *)
  val empty : world

  (* extend a development with a theorem *)
  val prove : world -> label * operator * judgement * tactic -> world

  (* extend a development with a custom tactic *)
  val defineTactic : world -> label * (world -> tactic) -> world

  (* extend a development with a new operator *)
  val declareOperator : world -> label * operator -> world
  val defineOperator : world -> {definiendum : term, definiens : term} -> world
  val declareNotation : world -> operator * Notation.t -> world

  (* declare a new resource with no registered tactics *)
  val declareResource : world -> resource -> world

  (* extend the resource pool with a new tactic *)
  val addResource : world -> resource * tactic -> world

  (* lookup the statement & evidence of a theorem *)
  val lookupTheorem : world -> operator -> {statement : judgement, evidence : evidence Susp.susp}
  val lookupExtract : world -> operator -> term

  (* lookup a custom tactic *)
  val lookupTactic : world -> label -> tactic

  (* lookup the definiens *)
  val lookupDefinition : world -> operator -> conv

  (* Lookup the collection of tactics for a given resource *)
  val lookupResource : world -> resource -> tactic list

  val lookupObject : world -> operator -> object
  val searchObject : world -> label -> (label * object) list
end
