signature DEVELOPMENT =
sig
  type term

  structure Lcf : LCF
  structure Telescope : TELESCOPE
  type label = Telescope.label

  type definition = {definiens : term}
  type theorem =
    {statement : Lcf.goal,
     script : Lcf.tactic,
     evidence : Lcf.evidence Susp.susp}

  type t

  datatype object =
      Definition of definition
    | Theorem of theorem
    | Tactic of Lcf.tactic

  val out : t -> object Telescope.telescope

  (* the empty development *)
  val empty : t

  (* extend a development with a definition *)
  val define : t -> label * term -> t

  (* extend a development with a theorem *)
  val prove : t -> label * Lcf.goal * Lcf.tactic -> t
  exception RemainingSubgoals of Lcf.goal list

  (* extend a development with a custom tactic *)
  val define_tactic : t -> label * Lcf.tactic -> t

  (* lookup the definiens *)
  val lookup_definition : t -> label -> term

  (* lookup the statement & evidence of a theorem *)
  val lookup_theorem : t -> label -> {statement : Lcf.goal, evidence : Lcf.evidence Susp.susp}

  (* lookup a custom tactic *)
  val lookup_tactic : t -> label -> Lcf.tactic
end
