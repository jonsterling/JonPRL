signature DEVELOPMENT =
sig
  type term

  structure Lcf : LCF
  structure ConvCompiler : CONV_COMPILER
  structure Telescope : TELESCOPE
  type label = Telescope.label

  sharing type ConvCompiler.Syntax.t = term

  structure Object :
  sig
    type t
    val to_string : label * t -> string
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
  val define_tactic : t -> label * Lcf.tactic -> t

  (* extend a development with a new operator *)
  val declare_operator : t -> label * int vector -> t
  val define_operator : t -> ConvCompiler.rule -> t

  (* lookup the definiens *)
  val lookup_definition : t -> label -> ConvCompiler.conv

  (* lookup the statement & evidence of a theorem *)
  val lookup_theorem : t -> label -> {statement : Lcf.goal, evidence : Lcf.evidence Susp.susp}

  (* lookup a custom tactic *)
  val lookup_tactic : t -> label -> Lcf.tactic

  (* lookup a custom operator *)
  val lookup_operator : t -> label -> int vector
end
