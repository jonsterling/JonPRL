signature DEVELOPMENT =
sig
  type label
  type term

  structure Lcf : LCF

  structure Telescope : TELESCOPE

  type definition = {definiens : term}
  type theorem =
    {statement : Lcf.goal,
     script : Lcf.tactic,
     evidence : Lcf.evidence Susp.susp}

  type t

  datatype object =
      Definition of definition
    | Theorem of theorem

  val out : t -> object Telescope.telescope

  (* the empty development *)
  val empty : t

  (* extend a development with a definition *)
  val define : t -> label * term -> t

  (* extend a development with a theorem *)
  val prove : t -> label * Lcf.goal * Lcf.tactic -> t
  exception RemainingSubgoals of Lcf.goal list

  (* lookup the definiens *)
  val lookup_definition : t -> label -> term

  (* lookup the statement & evidence of a theorem *)
  val lookup_theorem : t -> label -> {statement : Lcf.goal, evidence : Lcf.evidence Susp.susp}
end
