signature DEVELOPMENT =
sig
  type term

  structure Lcf : LCF
  structure PatternCompiler : PATTERN_COMPILER
  structure Telescope : TELESCOPE
  type label = Telescope.label

  sharing type PatternCompiler.term = term

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
  val prove : t -> label * Lcf.goal * Lcf.tactic -> t
  exception RemainingSubgoals of Lcf.goal list

  (* extend a development with a custom tactic *)
  val defineTactic : t -> label * Lcf.tactic -> t

  (* extend a development with a new operator *)
  val declareOperator : t -> label * Arity.t -> t
  val defineOperator : t -> PatternCompiler.rule -> t

  (* lookup the definiens *)
  val lookupDefinition : t -> label -> PatternCompiler.conv

  (* lookup the statement & evidence of a theorem *)
  val lookupTheorem : t -> label -> {statement : Lcf.goal, evidence : Lcf.evidence Susp.susp}

  (* lookup a custom tactic *)
  val lookupTactic : t -> label -> Lcf.tactic

  (* lookup a custom operator *)
  val lookupOperator : t -> label -> Arity.t
end
