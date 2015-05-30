signature LCF =
sig
  type goal
  type evidence

  type validation = evidence list -> evidence
  type tactic = goal -> goal list * validation

  val goal_to_string : goal -> string
end

