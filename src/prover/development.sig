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

  type conv = term -> term

  structure Telescope : TELESCOPE
  type label = Telescope.label

  structure Object :
  sig
    type theorem
    type operator_decl
    val operatorDeclArity : operator_decl -> Arity.t

    datatype t =
        THEOREM of theorem
      | TACTIC of tactic
      | OPERATOR of operator_decl

    val toString : label * t -> string
  end

  type object = Object.t

  (* enumerate the objects and knowledge available at a world *)
  val enumerate : world -> object Telescope.telescope
  val enumerateOperators : world -> (label * Arity.t) list
  val enumerateTactics : world -> label list

  (* the empty world *)
  val empty : world

  (* extend a development with a theorem *)
  val prove : world -> label * judgement * tactic -> world

  (* extend a development with a custom tactic *)
  val defineTactic : world -> label * tactic -> world

  (* extend a development with a new operator *)
  val declareOperator : world -> label * Arity.t -> world
  val defineOperator : world -> {definiendum : term, definiens : term} -> world

  (* lookup the statement & evidence of a theorem *)
  val lookupTheorem : world -> label -> {statement : judgement, evidence : evidence Susp.susp}
  val lookupExtract : world -> label -> term

  (* lookup a custom tactic *)
  val lookupTactic : world -> label -> tactic

  (* lookup a custom operator *)
  val lookupOperator : world -> label -> Arity.t

  (* lookup the definiens *)
  val lookupDefinition : world -> label -> conv

  val lookupObject : world -> label -> Object.t
end
